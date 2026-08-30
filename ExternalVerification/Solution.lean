/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification.Statements
import Erdos249257.BooleanMobiusCarry
import Erdos249257.BooleanMobiusSkipRowCofinal
import Erdos249257.TotientTailCarryPeriod
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.GcdMomentCalculus
import Erdos249257.LcmFactorIdealPulseObstruction
import Erdos249257.RationalSupportCarrySkeleton
import Erdos249257.CompositeDilationDefect
import Erdos249257.SupportSunflowerDichotomy
import Erdos249257.HalfGreedyTwoThirdsBand
import Erdos249257.SternBrocotRunGeometry
import Erdos249257.TotientKernelConditional
import Erdos249257.TotientMahlerDefect
import Erdos249257.TotientActualLcmOrbitNonintegrality
import Erdos249257.TotientActualLcmOrbitSeparation
import Erdos249257.FirstHarmonicPivot
import Erdos249257.TotientActualLcmOrbitSign
import Erdos249257.ActualForeignResidueProjection
import Erdos249257.TropicalCurvatureCarry
import ErdosProblems.Erdos68.FactorialZeroPlateau
import ErdosProblems.Erdos243.ReciprocalTailRigidity
import ErdosProblems.Erdos243.SparseResetRecovery
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import ErdosProblems.Erdos249.TotientStrictPrimeEscape
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos257.MersenneSubseriesRigidity
import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Erdos269.WeightedPhaseCarry
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation
import ErdosProblems.Erdos1049.RationalBaseLambert
import ErdosProblems.Erdos1049.HermitePadeNoGo

/-!
# Solutions for the external Comparator packet

These thin wrappers expose the configured existing results through the Mathlib-only
statement vocabulary in `ExternalVerification.Statements`.  They add no new
mathematical claim: each proof is a definitional transport from the declaration
owned by the public claim registry.
-/

namespace Erdos249257.ExternalVerification

open scoped ENNReal
open Module MeasureTheory

private theorem runBoundaryPair_eq_source (ns : List ℕ) :
    runBoundaryPair ns = SternBrocotRunGeometry.runBoundaryPair ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp [runBoundaryPair, SternBrocotRunGeometry.runBoundaryPair, ih]

private theorem periodLcm_eq_source (t : ℕ) :
    periodLcm t = Erdos249257.TotientTailPeriodKiller.periodLcm t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp [periodLcm,
        Erdos249257.TotientTailPeriodKiller.periodLcm, ih]

private theorem conditionalWindowBase_eq_source
    (b : ℕ → ℤ) (lo len : ℕ) :
    windowBase b lo len = ErdosProblems.Erdos269.windowBase b lo len := by
  induction len with
  | zero => rfl
  | succ len ih =>
      simp [windowBase, ErdosProblems.Erdos269.windowBase, ih]

private theorem conditionalWindowForcing_eq_source
    (b e : ℕ → ℤ) (lo len : ℕ) :
    windowForcing b e lo len =
      ErdosProblems.Erdos269.windowForcing b e lo len := by
  induction len with
  | zero => rfl
  | succ len ih =>
      simp [windowForcing, ErdosProblems.Erdos269.windowForcing, ih]

private theorem conditionalLeastPositiveResidue_eq_source
    (C : ℕ) (x : ℤ) :
    leastPositiveResidue C x =
      ErdosProblems.Erdos269.leastPositiveResidue C x := by
  rfl

private theorem totientTail_eq_source (N : ℕ) :
    totientTail N = Erdos249257.TotientTailPeriodKiller.totientTail N := by
  rfl

private theorem tailOrbitFirstExp_eq_source (h N : ℕ) :
    tailOrbitFirstExp h N =
      Erdos249257.TotientTailPeriodKiller.tailOrbitFirstExp h N := by
  rfl

private theorem TotientTailOrbitBlockGap_eq_source :
    TotientTailOrbitBlockGap ↔
      ErdosProblems.Erdos249.TotientTailOrbitBlockGap := by
  simp only [TotientTailOrbitBlockGap,
    ErdosProblems.Erdos249.TotientTailOrbitBlockGap,
    tailOrbitFirstExp_eq_source]

private theorem TotientTailOrbitNonpositiveBlockDensity_eq_source :
    TotientTailOrbitNonpositiveBlockDensity ↔
      ErdosProblems.Erdos249.TotientTailOrbitNonpositiveBlockDensity := by
  simp only [TotientTailOrbitNonpositiveBlockDensity,
    ErdosProblems.Erdos249.TotientTailOrbitNonpositiveBlockDensity,
    tailOrbitFirstExp_eq_source]

private theorem DTWNaturalPrimeTailOrbitStrictGap_eq_source :
    DTWNaturalPrimeTailOrbitStrictGap ↔
      ErdosProblems.Erdos249.DTWNaturalPrimeTailOrbitStrictGap := by
  simp only [DTWNaturalPrimeTailOrbitStrictGap,
    ErdosProblems.Erdos249.DTWNaturalPrimeTailOrbitStrictGap,
    tailOrbitFirstExp_eq_source]

private theorem actualLcmHeight_eq_source (a : ℕ) :
    actualLcmHeight a =
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight a := by
  simp [actualLcmHeight,
    Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight,
    periodLcm_eq_source]

private theorem actualLcmTailOrbit_eq_source (a : ℕ) :
    actualLcmTailOrbit a =
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit a := by
  simp only [actualLcmTailOrbit,
    Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit,
    totientTail_eq_source, actualLcmHeight_eq_source]

private theorem actualLcmOrbitSupply_eq_source :
    PowerTwoActualLcmOrbitNonintegralitySupply =
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmOrbitNonintegralitySupply := by
  apply propext
  constructor
  · intro h a₀
    obtain ⟨a, ha, hnon⟩ := h a₀
    refine ⟨a, ha, ?_⟩
    rw [actualLcmTailOrbit_eq_source] at hnon
    exact hnon
  · intro h a₀
    obtain ⟨a, ha, hnon⟩ := h a₀
    refine ⟨a, ha, ?_⟩
    rw [actualLcmTailOrbit_eq_source]
    exact hnon

private theorem actualLcmRawApprox_eq_source (a q : ℕ) :
    actualLcmRawApprox a q =
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawApprox a q := by
  simp [actualLcmRawApprox,
    Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawApprox,
    diagonalAdjacentSuffixRawBlock,
    Erdos249257.DiagonalFreshLossBridge.diagonalAdjacentSuffixRawBlock,
    diagonalWindowIncrement,
    Erdos249257.DiagonalFreshLossBridge.diagonalWindowIncrement,
    actualLcmHeight_eq_source, periodLcm_eq_source]

private theorem actualLcmRawErrorRadius_eq_source (a q : ℕ) :
    actualLcmRawErrorRadius a q =
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawErrorRadius a q := by
  simp [actualLcmRawErrorRadius,
    Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawErrorRadius,
    actualLcmHeight_eq_source, periodLcm_eq_source]

private theorem oddGuardedCanonicalAdjacentSuffixDepth_eq_source (t : ℕ) :
    oddGuardedCanonicalAdjacentSuffixDepth t =
      Erdos249257.DiagonalFreshLossBridge.oddGuardedCanonicalAdjacentSuffixDepth t := by
  simp [oddGuardedCanonicalAdjacentSuffixDepth,
    Erdos249257.DiagonalFreshLossBridge.oddGuardedCanonicalAdjacentSuffixDepth,
    canonicalAdjacentSuffixDepth,
    Erdos249257.DiagonalFreshLossBridge.canonicalAdjacentSuffixDepth,
    periodLcm_eq_source]

private theorem actualLcmOrbitSeparationSupply_eq_source :
    PowerTwoActualLcmOrbitSeparationSupply =
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmOrbitSeparationSupply := by
  apply propext
  constructor
  · intro h a₀
    obtain ⟨a, q, ha, hdepth, hsep⟩ := h a₀
    refine ⟨a, q, ha, ?_, ?_⟩
    · rw [oddGuardedCanonicalAdjacentSuffixDepth_eq_source] at hdepth
      exact hdepth
    · rw [actualLcmRawErrorRadius_eq_source,
        actualLcmTailOrbit_eq_source] at hsep
      exact hsep
  · intro h a₀
    obtain ⟨a, q, ha, hdepth, hsep⟩ := h a₀
    refine ⟨a, q, ha, ?_, ?_⟩
    · rw [oddGuardedCanonicalAdjacentSuffixDepth_eq_source]
      exact hdepth
    · rw [actualLcmRawErrorRadius_eq_source,
        actualLcmTailOrbit_eq_source]
      exact hsep

private theorem pivotOffset_eq_source (L s : ℕ) :
    pivotOffset L s =
      Erdos249257.TotientTailPeriodKiller.pivotOffset L s := by
  rfl

private theorem pivotArgument_eq_source (N L s : ℕ) :
    pivotArgument N L s =
      Erdos249257.TotientTailPeriodKiller.pivotArgument N L s := by
  rfl

private theorem pivotPrime_eq_source (N L s : ℕ) :
    pivotPrime N L s =
      Erdos249257.TotientTailPeriodKiller.pivotPrime N L s := by
  rfl

private theorem pivotCofactor_eq_source (N L s : ℕ) :
    pivotCofactor N L s =
      Erdos249257.TotientTailPeriodKiller.pivotCofactor N L s := by
  rfl

private theorem pivotSupplier_eq_source (X L s N : ℕ) :
    pivotSupplier X L s N =
      Erdos249257.TotientTailPeriodKiller.pivotSupplier X L s N := by
  rfl

private theorem pivotSupplierBases_eq_source (X L s : ℕ) :
    pivotSupplierBases X L s =
      Erdos249257.TotientTailPeriodKiller.pivotSupplierBases X L s := by
  rfl

private theorem pivotFiber_eq_source (X L s m : ℕ) :
    pivotFiber X L s m =
      Erdos249257.TotientTailPeriodKiller.pivotFiber X L s m := by
  rfl

private theorem pivotSupplierPrimes_eq_source (X L s m : ℕ) :
    pivotSupplierPrimes X L s m =
      Erdos249257.TotientTailPeriodKiller.pivotSupplierPrimes X L s m := by
  rfl

private theorem pivotBaseOfPrime_eq_source (L s m p : ℕ) :
    pivotBaseOfPrime L s m p =
      Erdos249257.TotientTailPeriodKiller.pivotBaseOfPrime L s m p := by
  rfl

private theorem windowDiscrepancy_eq_source (h N L : ℕ) :
    windowDiscrepancy h N L =
      Erdos249257.TotientTailPeriodKiller.windowDiscrepancy h N L := by
  rfl

private theorem deltaTotient_eq_source (h n : ℕ) :
    deltaTotient h n =
      Erdos249257.TotientTailPeriodKiller.deltaTotient h n := by
  rfl

private theorem carryOrbit_eq_source (h N : ℕ) (d : ℤ) (i : ℕ) :
    carryOrbit h N d i =
      Erdos249257.TotientTailPeriodKiller.carryOrbit h N d i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [carryOrbit,
        Erdos249257.TotientTailPeriodKiller.carryOrbit, ih,
        deltaTotient_eq_source]

private theorem endpointSurvivor_eq_source (h N L : ℕ) (z : ℤ) :
    endpointSurvivor h N L z =
      Erdos249257.TotientTailPeriodKiller.endpointSurvivor h N L z := by
  simp [endpointSurvivor,
    Erdos249257.TotientTailPeriodKiller.endpointSurvivor,
    windowDiscrepancy_eq_source]

private theorem dyadicClearedPrefix_eq_source
    (a : ℕ → ℤ) (n L : ℕ) :
    dyadicClearedPrefix a n L =
      Erdos249257.TotientTailPeriodKiller.dyadicClearedPrefix a n L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      simp [dyadicClearedPrefix,
        Erdos249257.TotientTailPeriodKiller.dyadicClearedPrefix, ih]

private theorem shiftLinearCombination_eq_source
    (terms : List (ℕ × ℤ)) (f : ℕ → ℤ) (n : ℕ) :
    shiftLinearCombination terms f n =
      Erdos249257.TotientTailPeriodKiller.shiftLinearCombination terms f n := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rcases term with ⟨h, q⟩
      simp [shiftLinearCombination,
        Erdos249257.TotientTailPeriodKiller.shiftLinearCombination, ih]

private theorem shiftLinearWeight_eq_source (terms : List (ℕ × ℤ)) :
    shiftLinearWeight terms =
      Erdos249257.TotientTailPeriodKiller.shiftLinearWeight terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rcases term with ⟨h, q⟩
      simp [shiftLinearWeight,
        Erdos249257.TotientTailPeriodKiller.shiftLinearWeight, ih]

private def orthogonalPetalBouquet_to_source {A : Set ℕ}
    (hB : OrthogonalPetalBouquet A) :
    Erdos249257.SupportSunflowerDichotomy.OrthogonalPetalBouquet A where
  Q := hB.Q
  Q_pos := hB.Q_pos
  exceptional := hB.exceptional
  core := hB.core
  petal := hB.petal
  exceptional_pos := hB.exceptional_pos
  exceptional_dvd_Q := hB.exceptional_dvd_Q
  core_pos := hB.core_pos
  core_dvd_Q := hB.core_dvd_Q
  petal_one_lt := hB.petal_one_lt
  petal_coprime_Q := hB.petal_coprime_Q
  petal_pairwise := hB.petal_pairwise
  support_eq := hB.support_eq
  summable_inv_petal := hB.summable_inv_petal

private theorem sunflowerForcedSlotTailSelection_to_source {A : Set ℕ}
    (hselection : SunflowerForcedSlotTailSelection A) :
    Erdos249257.SupportSunflowerDichotomy.SunflowerForcedSlotTailSelection A := by
  simpa [SunflowerForcedSlotTailSelection,
    Erdos249257.SupportSunflowerDichotomy.SunflowerForcedSlotTailSelection,
    supportCoeff, Erdos249257.supportCoeff,
    binaryCoeffTail, Erdos249257.binaryCoeffTail] using hselection

private theorem seamWeightsFrom_eq_source (s d : ℕ) :
    seamWeightsFrom s d =
      Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom s d := by
  by_cases hds : d < s
  · rw [seamWeightsFrom, dif_pos hds,
      Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, dif_pos hds]
    congr 1
    exact seamWeightsFrom_eq_source s (d + 1)
  · rw [seamWeightsFrom, dif_neg hds,
      Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, dif_neg hds]

private theorem seamWeights_eq_source (s : ℕ) :
    seamWeights s = Erdos249257.HalfCylinderIntegerGreedy.seamWeights s := by
  unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights
  exact seamWeightsFrom_eq_source s 2

private theorem seamIntegerGreedyBits_eq_source
    (weights : List ℕ) (C : ℕ) :
    seamIntegerGreedyBits weights C =
      Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits weights C := by
  induction weights generalizing C with
  | nil => rfl
  | cons w ws ih =>
      rw [seamIntegerGreedyBits,
        Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits]
      by_cases hw : w ≤ C
      · rw [if_pos hw, if_pos hw]
        congr 1
        exact ih (C - w)
      · rw [if_neg hw, if_neg hw]
        congr 1
        exact ih C

private theorem seamOfList_eq_source {s : ℕ} {a b : List Bool}
    (hab : a = b) (ha : a.length = s - 2) (hb : b.length = s - 2) :
    SeamRowWord.ofList a ha =
      Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList b hb := by
  subst b
  funext i
  rfl

private theorem seamGreedyWord_eq_source (s : ℕ) :
    seamGreedyWord s =
      Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord s := by
  have hbits :
      seamIntegerGreedyBits (seamWeights s) (seamSubsetTarget s) =
        Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits
          (Erdos249257.HalfCylinderIntegerGreedy.seamWeights s)
          (Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget s) := by
    rw [seamWeights_eq_source]
    exact seamIntegerGreedyBits_eq_source _ _
  unfold seamGreedyWord
    Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord
  exact seamOfList_eq_source hbits _ _

private theorem seamTerminal_eq_source (s : ℕ) (hs : 3 ≤ s) :
    SeamRowWord.terminal hs (seamGreedyWord (s + 1)) =
      Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.terminal hs
        (Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord (s + 1)) := by
  rw [seamGreedyWord_eq_source]
  rfl

private theorem seamUnboundedTerminalFalse_eq_source :
    SeamGreedyUnboundedTerminalFalse ↔
      Erdos249257.SeamGreedyUnboundedTerminalFalse := by
  constructor
  · intro h N
    obtain ⟨p, hp5, hNp, hfalse⟩ := h N
    refine ⟨p, hp5, hNp, ?_⟩
    rw [← seamTerminal_eq_source]
    exact hfalse
  · intro h N
    obtain ⟨p, hp5, hNp, hfalse⟩ := h N
    refine ⟨p, hp5, hNp, ?_⟩
    rw [seamTerminal_eq_source]
    exact hfalse

/-! The statement-only packet owns isomorphic copies of the finite index
types, because `Statements.lean` must not import proof-bearing source modules.
This equivalence is the explicit transport boundary for the all-base rank
claim. -/
def totientKernelHeadIndexEquiv :
    TotientKernelHeadIndex ≃ Erdos249257.TotientKernelHeadIndex where
  toFun
    | .F00 => .F00
    | .F10 => .F10
  invFun
    | .F00 => .F00
    | .F10 => .F10
  left_inv := by
    intro i
    cases i <;> rfl
  right_inv := by
    intro i
    cases i <;> rfl

def totientKernelIndexEquiv (k e : ℕ) :
    TotientKernelIndex k e ≃ Erdos249257.TotientKernelIndex k e :=
  totientKernelHeadIndexEquiv.sumCongr (Equiv.refl _)

set_option maxHeartbeats 1000000 in
theorem portfolioClaims (ι : Type*) [Fintype ι] : PortfolioClaims ι := by
  constructor
  · simpa [factorialGapSeries, factorialGapTail, factorialGapTailTerm,
      strictFacTopRat, factorialGapPrefix,
      Erdos68.factorialGapSeries, Erdos68.factorialGapTail,
      Erdos68.factorialGapTailTerm,
      ErdosProblems.Erdos68.strictFacTopRat,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses
  · simpa [factorialGapSeries, factorialGapTail, factorialGapTailTerm,
      factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      factorialGapPrefix,
      Erdos68.factorialGapSeries, Erdos68.factorialGapTail,
      Erdos68.factorialGapTailTerm,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_nonunit_carries
  · intro a C D magnitude B hB ha hCpos hC hD hRise hmagnitude hvanish hnegative
    exact ErdosProblems.Erdos243.no_cofinallyBoundedNegative_of_normalizedVanishes
      a C D magnitude B hB ha hCpos hC hD hRise hmagnitude hvanish hnegative
  · exact ErdosProblems.Erdos243.no_eventuallyPeriodicNegative_orbit
  · intro u m N B hB hm hpair havoid hrise huTop
    exact ErdosProblems.Erdos243.no_boundedRise_of_tailAvoidance
      u m N B hB hm hpair havoid hrise huTop
  · intro a D C hD hC hE hCne
    simpa [sylvesterNext, nextDenState, nextTailState, centeredState,
      ErdosProblems.Erdos243.sylvesterNext,
      ErdosProblems.Erdos243.nextDenState,
      ErdosProblems.Erdos243.nextTailState,
      ErdosProblems.Erdos243.centeredState] using
      ErdosProblems.Erdos243.sylvesterNext_eventually_of_centered_zero
        a D C hD hC hE hCne
  · intro C E hrec
    exact ErdosProblems.Erdos243.centeredState_eventually_zero C E hrec
  · intro a C D E B ha hCpos hC hD hE hcentered hbound hvanish
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using
      ErdosProblems.Erdos243.boundedNegativePart_eventually_zero
        a C D E B ha hCpos hC hD hE hcentered hbound hvanish
  · intro a D C hD hC hCpos hstep hvanish hsum
    simpa [negativeRelativeMass, sylvesterNext, nextDenState, nextTailState,
      centeredState, ErdosProblems.Erdos243.negativeRelativeMass,
      ErdosProblems.Erdos243.sylvesterNext,
      ErdosProblems.Erdos243.nextDenState,
      ErdosProblems.Erdos243.nextTailState,
      ErdosProblems.Erdos243.centeredState] using
      ErdosProblems.Erdos243.sylvesterNext_eventually_of_summable_negativeRelativeMass
        a D C hD hC hCpos hstep hvanish hsum
  · intro e he
    simpa [totientKernelThroughLevelFamily, totientKernelSeq,
      Erdos249257.totientKernelThroughLevelFamily,
      Erdos249257.totientKernelSeq] using
      Erdos249257.finrank_totientKernelThroughLevelFamily_eq e he
  · simpa [fullTotientKernelFamily, totientKernelSeq,
      Erdos249257.fullTotientKernelFamily,
      Erdos249257.totientKernelSeq] using
      Erdos249257.not_finiteDimensional_span_fullTotientKernel
  · refine ⟨?_⟩
    simpa [TotientOddCoreIndex, fullTotientKernelFamily, totientKernelSeq,
      Erdos249257.TotientOddCoreIndex,
      Erdos249257.fullTotientKernelFamily,
      Erdos249257.totientKernelSeq] using
      Erdos249257.totientDyadicSectionBasis
  · intro k e hk he hcanon
    have hcanon' :
        LinearIndependent ℚ (Erdos249257.canonicalAllBaseTotientKernelFamily k e) := by
      refine (linearIndependent_equiv' (totientKernelIndexEquiv k e) ?_).mp hcanon
      funext i
      cases i with
      | inl i =>
          cases i <;>
            simp [Function.comp_def, canonicalAllBaseTotientKernelFamily,
              allBaseTotientKernelSeq, totientKernelIndexEquiv,
              totientKernelHeadIndexEquiv,
              Erdos249257.canonicalAllBaseTotientKernelFamily,
              Erdos249257.allBaseTotientKernelSeq]
          all_goals
            funext n
            rfl
      | inr i =>
          simp [Function.comp_def, canonicalAllBaseTotientKernelFamily,
            allBaseTotientKernelSeq, totientKernelSectionLevel,
            totientKernelSectionResidue, totientKernelIndexEquiv,
            totientKernelHeadIndexEquiv,
            Erdos249257.canonicalAllBaseTotientKernelFamily,
            Erdos249257.allBaseTotientKernelSeq,
            Erdos249257.totientKernelSectionLevel,
            Erdos249257.totientKernelSectionResidue]
          funext n
          rfl
    simpa [allBaseTotientKernelThroughLevelFamily, allBaseTotientKernelSeq,
      AllBaseTotientKernelThroughLevelIndex,
      Erdos249257.allBaseTotientKernelThroughLevelFamily,
      Erdos249257.allBaseTotientKernelSeq,
      Erdos249257.AllBaseTotientKernelThroughLevelIndex] using
      Erdos249257.finrank_allBaseTotientKernelThroughLevelFamily_eq_of_linearIndependent
        k e hk he hcanon'
  · intro hirr
    simpa [binaryCoeffSeries, IsTemperedBinaryOrbit,
      CarrySectionsEventuallyPeriodicMod, carryKernelSeq,
      canonicalCarryKernelFamily, Erdos249257.binaryCoeffSeries,
      Erdos249257.IsTemperedBinaryOrbit,
      Erdos249257.CarrySectionsEventuallyPeriodicMod,
      Erdos249257.carryKernelSeq,
      Erdos249257.canonicalCarryKernelFamily] using
      Erdos249257.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
        hirr
  · intro u hu symbols hodd e
    let toSource : VUSymbol → Erdos249257.TotientTailPeriodKiller.VUSymbol :=
      fun σ => { valuation := σ.valuation, unit := σ.unit }
    have hcompatible (σ : VUSymbol) (c : ℤ) :
        VUCompatible u σ c ↔
          Erdos249257.TotientTailPeriodKiller.VUCompatible u (toSource σ) c := by
      rfl
    have hradius (σ : VUSymbol) :
        vuRadius u σ =
          Erdos249257.TotientTailPeriodKiller.vuRadius u (toSource σ) := by
      rfl
    have hodd' :
        ∀ σ ∈ symbols.map toSource,
          Odd σ.unit := by
      intro σ hσ
      rcases List.mem_map.1 hσ with ⟨τ, hτ, rfl⟩
      exact hodd τ hτ
    have orbit_to_source
        {e : ℤ} {ss : List VUSymbol} {states : List ℤ}
        (horbit : VUOrbit u e ss states) :
        Erdos249257.TotientTailPeriodKiller.VUOrbit u e (ss.map toSource) states := by
      induction horbit with
      | nil e =>
          exact Erdos249257.TotientTailPeriodKiller.VUOrbit.nil e
      | cons e c e' σ ss states hcompat' hstep htail ih =>
          exact Erdos249257.TotientTailPeriodKiller.VUOrbit.cons e c e'
            (toSource σ) (ss.map toSource) states
            ((hcompatible σ c).mp hcompat') hstep ih
    have orbit_of_source
        {e : ℤ} {ss : List VUSymbol} {states : List ℤ}
        (horbit :
          Erdos249257.TotientTailPeriodKiller.VUOrbit u e (ss.map toSource) states) :
        VUOrbit u e ss states := by
      induction ss generalizing e states with
      | nil =>
          cases horbit
          exact VUOrbit.nil e
      | cons σ ss ih =>
          cases horbit with
          | cons e c e' σ' ss' states hcompat' hstep htail =>
              exact VUOrbit.cons e c e' σ ss states
                ((hcompatible σ c).mpr hcompat') hstep (ih htail)
    obtain ⟨states, horbit, hbounds⟩ :=
      Erdos249257.TotientTailPeriodKiller.fixedPrecisionTropicalNoGo
        u hu (symbols.map toSource) hodd' e
    refine ⟨states, orbit_of_source horbit, ?_⟩
    simpa [hradius] using hbounds
  · intro h N₀ hh
    simpa [binaryCyclotomicLayer,
      ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
      ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_clean_binaryCyclotomicAnchor
        h N₀ hh
  · intro B hB base carry digit hrec
    simpa [weightedCarryResidue, weightedCarryQuotient,
      weightedResidueDigit, ErdosProblems.Erdos269.carryResidue,
      ErdosProblems.Erdos269.carryQuotient,
      ErdosProblems.Erdos269.residueDigit] using
      ErdosProblems.Erdos269.carry_eq_residueDigit_add_coboundary
        B hB base carry digit hrec
  · intro b m shortBound hescape B hBpos hBcoprime d hrec hpos hbound
    have hescape' :
        ErdosProblems.Erdos269.CofinalLocalWindowEscape b m shortBound := by
      simpa only [CofinalLocalWindowEscape,
        ErdosProblems.Erdos269.CofinalLocalWindowEscape,
        conditionalWindowBase_eq_source,
        conditionalWindowForcing_eq_source,
        conditionalLeastPositiveResidue_eq_source] using hescape
    simpa using
      ErdosProblems.Erdos269.no_positive_reducedCarry_of_cofinalLocalWindowEscape
        b m shortBound hescape' B hBpos hBcoprime d hrec hpos hbound
  · exact GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one
  · exact GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series
  · intro e
    have hsource := SternBrocotRunGeometry.runHeight_defect_fib_sum_lower e
    simpa [runHeight, SternBrocotRunGeometry.runHeight,
      defectRunLengths, SternBrocotRunGeometry.defectRunLengths,
      runBoundaryPair_eq_source] using hsource
  · intro a b
    simpa [cylinderMass, GcdMomentCalculus.cylinderMass] using
      GcdMomentCalculus.cylinderMass_split a b
  · intro t ht
    simpa only [dyadicCoboundary,
      Erdos249257.TotientTailPeriodKiller.dyadicCoboundary,
      periodLcm_eq_source, dyadicClearedPrefix_eq_source,
      shiftLinearCombination_eq_source, shiftLinearWeight_eq_source] using
      Erdos249257.TotientTailPeriodKiller.lcm_factorIdeal_finiteRank_shiftAlgebra_not_sufficient
        t ht
  · rw [actualLcmOrbitSupply_eq_source]
    exact
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply
  · intro hsupply
    apply
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply
    rw [← actualLcmOrbitSupply_eq_source]
    exact hsupply
  · intro hsupply
    apply
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.irrational_totientSeries_of_actualLcmOrbitSeparationSupply
    rw [← actualLcmOrbitSeparationSupply_eq_source]
    exact hsupply
  · intro X L s m hm hmsmall
    change
      (Erdos249257.TotientTailPeriodKiller.pivotSupplierPrimes X L s m).image
          (Erdos249257.TotientTailPeriodKiller.pivotBaseOfPrime L s m) =
        Erdos249257.TotientTailPeriodKiller.pivotFiber X L s m
    exact
      Erdos249257.TotientTailPeriodKiller.image_pivotSupplierPrimes_eq_pivotFiber
        hm hmsmall
  · change
      Erdos249257.TotientTailPeriodKiller.pivotOffset 20 1 = 20 ∧
        18 ∈ Erdos249257.TotientTailPeriodKiller.pivotFiber 16 20 1 2 ∧
        Erdos249257.TotientTailPeriodKiller.pivotPrime 18 20 1 = 19 ∧
        19 ∣ Erdos249257.TotientTailPeriodKiller.pivotArgument 18 20 1 ∧
        19 ∣ 18 + 1
    exact
      Erdos249257.TotientTailPeriodKiller.supplierPrime_not_globally_isolated_counterexample
  · intro h X L s η
    change
      (∑ N ∈ Finset.Ico X (2 * X),
          Erdos249257.TotientTailPeriodKiller.windowFirstExp h N L) =
        Erdos249257.TotientTailPeriodKiller.pivotCenteredCorrelation h X L s η +
        Erdos249257.TotientTailPeriodKiller.pivotFiberMeanContribution h X L s η +
        Erdos249257.TotientTailPeriodKiller.pivotBadContribution h X L s η +
        Erdos249257.TotientTailPeriodKiller.pivotNonSupplierContribution h X L s
    exact
      Erdos249257.TotientTailPeriodKiller.windowFirstExp_sum_eq_pivot_decomposition
        h X L s η
  · intro h X L s η hbudget
    exact
      Erdos249257.TotientTailPeriodKiller.first_harmonic_gap_of_pivotBudgetAt
        hbudget
  · intro hmix
    exact
      Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotResidualDecorrelation
        hmix
  · intro a J ha hshort
    rw [totientTail_eq_source, periodLcm_eq_source]
    exact
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailDiff_shift_pos
        ha hshort
  · intro a J K ha hshort d hd
    have hd' : (d : ℝ) =
        Erdos249257.TotientTailPeriodKiller.totientTail
            (2 * Erdos249257.TotientTailPeriodKiller.periodLcm (2 ^ a) + J) -
          Erdos249257.TotientTailPeriodKiller.totientTail
            (Erdos249257.TotientTailPeriodKiller.periodLcm (2 ^ a) + J) := by
      simpa only [totientTail_eq_source, periodLcm_eq_source] using hd
    exact
      (by
        simpa only [periodLcm_eq_source, carryOrbit_eq_source,
          endpointSurvivor_eq_source] using
          (Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcm_trueEndpointSurvivor_neg
            ha hshort hd'))
  · intro a J K ha hshort d hd hroom
    have hd' : (d : ℝ) =
        Erdos249257.TotientTailPeriodKiller.totientTail
            (2 * Erdos249257.TotientTailPeriodKiller.periodLcm (2 ^ a) + J) -
          Erdos249257.TotientTailPeriodKiller.totientTail
            (Erdos249257.TotientTailPeriodKiller.periodLcm (2 ^ a) + J) := by
      simpa only [totientTail_eq_source, periodLcm_eq_source] using hd
    have hroom' :
        ((2 * Erdos249257.TotientTailPeriodKiller.periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
          (2 : ℤ) ^ K := by
      simpa only [periodLcm_eq_source] using hroom
    exact
      (by
        simpa only [periodLcm_eq_source, windowDiscrepancy_eq_source,
          carryOrbit_eq_source] using
          (Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcm_integral_forces_topEdgeResidue
            ha hshort hd' hroom'))
  · constructor
    · intro H D L hcutoff
      exact
        Erdos249257.ActualForeignResidueProjection.abs_foreignTailWindow_le_foreignComplementBound
          hcutoff
    · constructor
      · intro H D
        exact
          Erdos249257.ActualForeignResidueProjection.finiteResidueDiagonal_eq_projectedForeign_add_divisor
            H D
      · intro H D hcontrol hseparation
        exact
          Erdos249257.ActualForeignResidueProjection.scaleFullTarget_miss_of_projected_separation
            hcontrol hseparation
  · intro M
    simpa [primeGap0, prime0, ErdosProblems.Erdos251.primeGap0,
      ErdosProblems.Erdos251.prime0] using
      ErdosProblems.Erdos251.exists_primeGap0_gt M
  · refine ⟨?_, ?_, ?_⟩
    · intro n
      simpa [carryPartialSum, carryCoeff,
        ErdosProblems.Erdos251.carryPartialSum,
        ErdosProblems.Erdos251.carryCoeff] using
        ErdosProblems.Erdos251.carryPartialSum_natCast_eq n
    · intro h hpos
      simpa [carryCoeff, ErdosProblems.Erdos251.carryCoeff] using
        ErdosProblems.Erdos251.carryCoeff_natCast_not_eventually_periodic hpos
    · intro h hpos
      simpa [primeGap0, prime0, ErdosProblems.Erdos251.primeGap0,
        ErdosProblems.Erdos251.prime0] using
        ErdosProblems.Erdos251.primeGap0_not_eventually_periodic hpos
  · intro T h hrec hsupply
    simpa [DyadicTailRecurrence, tailShift, RatIntegral, primeGap0, prime0,
      ErdosProblems.Erdos251.DyadicTailRecurrence,
      ErdosProblems.Erdos251.tailShift,
      ErdosProblems.Erdos251.RatIntegral,
      ErdosProblems.Erdos251.primeGap0,
      ErdosProblems.Erdos251.prime0] using
      ErdosProblems.Erdos251.primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch
        h hrec hsupply
  · intro hprime
    simpa [primeDyadicTerm, primeGapDyadicTerm, primeGap0, prime0,
      ErdosProblems.Erdos251.primeDyadicTerm,
      ErdosProblems.Erdos251.primeGapDyadicTerm,
      ErdosProblems.Erdos251.primeGap0,
      ErdosProblems.Erdos251.prime0] using
      ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap hprime
  · intro g T hrec N h
    simpa [DyadicTailRecurrence, tailShift, RatIntegral,
      ErdosProblems.Erdos251.DyadicTailRecurrence,
      ErdosProblems.Erdos251.tailShift,
      ErdosProblems.Erdos251.RatIntegral] using
      ErdosProblems.Erdos251.tailShift_integral_iff_den_dvd_mersenne
        hrec N h
  · intro g T hrec N h
    simpa [DyadicTailRecurrence, tailShift, RatIntegral,
      ErdosProblems.Erdos251.DyadicTailRecurrence,
      ErdosProblems.Erdos251.tailShift,
      ErdosProblems.Erdos251.RatIntegral] using
      ErdosProblems.Erdos251.tailShift_integral_iff_two_pow_modEq_one
        hrec N h
  · intro g T hrec
    simpa [RealDyadicTailRecurrence, realTailShift, RealIntegral,
      ErdosProblems.Erdos251.RealDyadicTailRecurrence,
      ErdosProblems.Erdos251.realTailShift,
      ErdosProblems.Erdos251.RealIntegral] using
      ErdosProblems.Erdos251.not_irrational_initial_iff_exists_eventually_integral_positive_tailShift
        hrec
  · intro g T hrec
    simpa [RealDyadicTailRecurrence, realTailShift, RealIntegral,
      ErdosProblems.Erdos251.RealDyadicTailRecurrence,
      ErdosProblems.Erdos251.realTailShift,
      ErdosProblems.Erdos251.RealIntegral] using
      ErdosProblems.Erdos251.irrational_initial_iff_all_positive_tailShifts_nonintegral
        hrec
  · simpa [mersenneAchievementSet, positiveMersenneSupportValue, mersenneWeight,
      Erdos249257.mersenneAchievementSet,
      Erdos249257.positiveMersenneSupportValue,
      Erdos249257.mersenneWeight] using
      Erdos249257.volume_mersenneAchievementSet
  · intro b hb
    simpa using Erdos249257.irrational_erdosSum_full_support b hb
  · intro b A hb hA hpair hsum
    simpa [erdosSupportSeries, Erdos249257.erdosSupportSeries] using
      Erdos249257.irrational_erdosSupportSeries_pairwise_coprime
        b A hb hA hpair hsum
  · intro b m N₀ γ hb hm hγ0 hper hpos
    simpa using
      Erdos249257.irrational_ratWeightSeries_eventuallyPeriodic
        b m N₀ γ hb hm hγ0 hper hpos
  · intro A hB hselection
    have hB' := orthogonalPetalBouquet_to_source hB
    have hselection' := sunflowerForcedSlotTailSelection_to_source hselection
    simpa [erdosSupportSeries, Erdos249257.erdosSupportSeries] using
      Erdos249257.SupportSunflowerDichotomy.irrational_erdosSupportSeries_of_orthogonalPetalBouquet
        hB' hselection'
  · intro F b hF h0 hb hcop
    simpa [finiteErdosSum, Erdos249257.finiteErdosSum] using
      Erdos249257.finite_period_noncollapse_rat_den F b hF h0 hb
  · intro J
    simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
      SupportedMersenneDigits, positiveMersenneDigitValue, mersenneDigitTerm,
      mersenneWeight,
      ErdosProblems.Erdos257.supportedMersenneAchievementSet,
      ErdosProblems.Erdos257.supportedMersenneDigitValue,
      ErdosProblems.Erdos257.SupportedMersenneDigits,
      Erdos249257.positiveMersenneDigitValue,
      Erdos249257.mersenneDigitTerm,
      Erdos249257.mersenneWeight] using
      ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy J
  · intro A hA p c v hv hvalue
    simpa [supportCoeff, erdosSupportSeries, binaryCoeffTail,
      Erdos249257.supportCoeff, Erdos249257.erdosSupportSeries,
      Erdos249257.binaryCoeffTail] using
      Erdos249257.exists_shifted_odd_tail_nat_states_of_support_fraction
        A hA p c v hv hvalue
  · intro p q hq
    constructor
    · intro h
      have hsource :
          (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
            Erdos249257.erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) := by
        simpa [erdosSupportSeries, Erdos249257.erdosSupportSeries] using h
      rcases
          (Erdos249257.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
            p q hq).mp hsource with ⟨U, hU⟩
      refine ⟨U, ?_⟩
      refine
        { initial := hU.initial
          positive := hU.positive
          sqrtBound := hU.sqrtBound
          divisible := hU.divisible
          mobiusBoolean := ?_ }
      intro n hn
      simpa [carryQuotientAF, carryQuotient,
        Erdos249257.carryQuotientAF, Erdos249257.carryQuotient] using
        hU.mobiusBoolean n hn
    · rintro ⟨U, hU⟩
      have hsource :
          ∃ U : ℕ → ℤ,
            Erdos249257.BooleanMobiusCarryCertificate p q U := by
        refine ⟨U, ?_⟩
        refine
          { initial := hU.initial
            positive := hU.positive
            sqrtBound := hU.sqrtBound
            divisible := hU.divisible
            mobiusBoolean := ?_ }
        intro n hn
        simpa [carryQuotientAF, carryQuotient,
          Erdos249257.carryQuotientAF, Erdos249257.carryQuotient] using
          hU.mobiusBoolean n hn
      have hresult :=
        (Erdos249257.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
          p q hq).mpr hsource
      simpa [erdosSupportSeries, Erdos249257.erdosSupportSeries] using hresult
  · intro hskips
    have hrem (x : ℚ) (n : ℕ) :
        greedyMersenneRemainderRat x n =
          Erdos249257.greedyMersenneRemainderRat x n := by
      induction n with
      | zero => rfl
      | succ n ih =>
          simp [greedyMersenneRemainderRat,
            Erdos249257.greedyMersenneRemainderRat, ih,
            mersenneWeightRat, Erdos249257.mersenneWeightRat]
    have hskips' : Erdos249257.CofinalPositiveHalfGreedySkips := by
      intro N
      rcases hskips N with ⟨c, hc, hpos, hskip⟩
      refine ⟨c, hc, ?_, ?_⟩
      · rw [← hrem (1 / 2 : ℚ) (c - 1)]
        exact hpos
      · rw [← hrem (1 / 2 : ℚ) (c - 1)]
        change greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
          mersenneWeightRat c
        exact hskip
    have hhalf :=
      Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
        hskips'
    simpa [mersenneAchievementSet, positiveMersenneSupportValue, mersenneWeight,
      Erdos249257.mersenneAchievementSet,
      Erdos249257.positiveMersenneSupportValue,
      Erdos249257.mersenneWeight] using hhalf
  · constructor
    · intro hhalf
      have hhalf' : (1 / 2 : ℝ) ∈ Erdos249257.mersenneAchievementSet := by
        simpa [mersenneAchievementSet, positiveMersenneSupportValue, mersenneWeight,
          Erdos249257.mersenneAchievementSet,
          Erdos249257.positiveMersenneSupportValue,
          Erdos249257.mersenneWeight] using hhalf
      exact seamUnboundedTerminalFalse_eq_source.mpr
        (Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse.mp
          hhalf')
    · intro hterminal
      have hterminal' := seamUnboundedTerminalFalse_eq_source.mp hterminal
      have hhalf' :=
        Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse.mpr
          hterminal'
      simpa [mersenneAchievementSet, positiveMersenneSupportValue, mersenneWeight,
        Erdos249257.mersenneAchievementSet,
        Erdos249257.positiveMersenneSupportValue,
        Erdos249257.mersenneWeight] using hhalf'
  · intro A a x ha ha0 hx0
    simpa [supportCoeff, compositeDilationDefect,
      Erdos249257.supportCoeff,
      Erdos249257.CompositeDilationDefect.compositeDilationDefect] using
      Erdos249257.CompositeDilationDefect.supportCoeff_mul_eq_add_defect
        A ha ha0 hx0
  · intro p D q hp hD hq hpodd hDodd hqodd hband
    simpa [IntBand, Erdos249257.HalfGreedyTwoThirdsBand.IntBand] using
      Erdos249257.HalfGreedyTwoThirdsBand.seven_le_of_intBand_odd
        hp hD hq hpodd hDodd hqodd hband
  · simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.threePrimeKernelQ,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.kernel_235_minor_eq_neg_one_fifteen
  · intro p q r x hp hq hr hpq hpr hqr hx
    simpa [smoothPrefixLcm, smoothPrefixExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.smoothPrefixLcm,
      ErdosProblems.Erdos269.smoothPrefixExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.smoothPrefixLcm_eq_threePrimeHeight
        hp hq hr hpq hpr hqr hx
  · intro p q r hp hq hr
    simpa [smoothExponentBox, smoothPointHeight, smoothHeightFiber,
      threePrimeKernelQ, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.smoothExponentBox,
      ErdosProblems.Erdos269.smoothPointHeight,
      ErdosProblems.Erdos269.smoothHeightFiber,
      ErdosProblems.Erdos269.threePrimeKernelQ,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.finiteSmoothKernelSum_groupedByHeight
        p q r hp hq hr
  · intro c hc ε hε
    simpa [SamePositiveRay, ErdosProblems.Erdos1041.SamePositiveRay] using
      ErdosProblems.Erdos1041.exists_small_translation_separating_arguments c hc hε
  · exact ErdosProblems.Erdos1041.constant_perturbation_roots_in_unitDisk
  · intro N K Q digit hN hK
    simpa [CoordinatewiseCorridor,
      ErdosProblems.Erdos1049.CoordinatewiseCorridor] using
      ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor
        (N := N) (K := K) (Q := Q) (digit := digit) hN hK
  · intro r s B F coeff hr N
    simpa [rationalBaseClearedTailQ, rationalBasePrefixQ,
      ErdosProblems.Erdos1049.rationalBaseClearedTailQ,
      ErdosProblems.Erdos1049.rationalBasePrefixQ] using
      ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ
        (r := r) (s := s) (B := B) (F := F) (coeff := coeff) hr N
  · intro rho sigma hrho hsigma
    simpa [hpClearedGap, hpDecay, hpHeight, hpCyclotomicSaving,
      ErdosProblems.Erdos1049.hpClearedGap,
      ErdosProblems.Erdos1049.hpDecay,
      ErdosProblems.Erdos1049.hpHeight,
      ErdosProblems.Erdos1049.hpCyclotomicSaving] using
      ErdosProblems.Erdos1049.hpClearedGap_nonpos rho sigma hrho hsigma
  · intro rho sigma hrho hsigma
    simpa [hpClearedGap, hpDecay, hpHeight, hpCyclotomicSaving,
      ErdosProblems.Erdos1049.hpClearedGap,
      ErdosProblems.Erdos1049.hpDecay,
      ErdosProblems.Erdos1049.hpHeight,
      ErdosProblems.Erdos1049.hpCyclotomicSaving] using
      ErdosProblems.Erdos1049.hpClearedGap_eq_zero_iff rho sigma hrho hsigma
  · intro rho sigma hrho hsigma
    simpa [hpThreshold, hpDecay, hpHeight, hpCyclotomicSaving,
      ErdosProblems.Erdos1049.hpThreshold,
      ErdosProblems.Erdos1049.hpDecay,
      ErdosProblems.Erdos1049.hpHeight,
      ErdosProblems.Erdos1049.hpCyclotomicSaving] using
      ErdosProblems.Erdos1049.rectangular_hp_threshold_le_classical rho sigma
        hrho hsigma
  · intro rho sigma hrho hsigma
    simpa [hpThreshold, hpDecay, hpHeight, hpCyclotomicSaving,
      ErdosProblems.Erdos1049.hpThreshold,
      ErdosProblems.Erdos1049.hpDecay,
      ErdosProblems.Erdos1049.hpHeight,
      ErdosProblems.Erdos1049.hpCyclotomicSaving] using
      ErdosProblems.Erdos1049.rectangular_hp_threshold_eq_classical_iff rho sigma
        hrho hsigma
  · intro hdensity
    exact TotientTailOrbitBlockGap_eq_source.mpr
      (ErdosProblems.Erdos249.tailOrbitBlockGap_of_nonpositiveBlockDensity
        (TotientTailOrbitNonpositiveBlockDensity_eq_source.mp hdensity))
  · intro hgap
    exact ErdosProblems.Erdos249.irrational_totient_series_of_tailOrbitBlockGap
      (TotientTailOrbitBlockGap_eq_source.mp hgap)
  · intro hgap
    exact ErdosProblems.Erdos249.irrational_totient_series_of_naturalPrimeTailOrbitStrictGap
      (DTWNaturalPrimeTailOrbitStrictGap_eq_source.mp hgap)

/-! These declarations are the proof-bearing Solution-side names consumed by
the Comparator roster.  Each is a projection of the corresponding field of
the exact `PortfolioClaims` proof above. -/

theorem not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u :=
  (portfolioClaims Unit).problem249CarryAntiCompression hirr

theorem fixedPrecisionTropicalNoGo
    (u : ℕ) (hu : 0 < u)
    (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ) :
    ∃ states : List ℤ,
      VUOrbit u e symbols states ∧
      List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states :=
  (portfolioClaims Unit).problem249FixedPrecisionTropicalNoGo
    u hu symbols hodd e

theorem exists_clean_binaryCyclotomicAnchor
    (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ binaryCyclotomicLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 :=
  (portfolioClaims Unit).problem249CleanBinaryCyclotomicAnchor h N₀ hh

theorem irrational_totientSeries_of_actualLcmOrbitSeparationSupply
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  (portfolioClaims Unit).problem249ActualLcmOrbitSeparation hsupply

theorem irrational_initial_iff_all_positive_tailShifts_nonintegral
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        ¬ RealIntegral (realTailShift T h N) :=
  (portfolioClaims Unit).problem251TailShiftIrrationalityNormalForm hrec

theorem exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U :=
  (portfolioClaims Unit).problem257BooleanMobiusCarry p q hq

theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  (portfolioClaims Unit).problem257BooleanMobiusExactRowDynamics hskips

theorem half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedTerminalFalse :=
  (portfolioClaims Unit).problem257HalfMembershipSeamClassification

theorem rectangular_hp_threshold_eq_classical_iff
    (rho sigma : ℝ) (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔
      rho = 0 ∧ sigma = 1 :=
  (portfolioClaims Unit).problem1049RectangularHpThresholdEqClassicalIff rho sigma
    hrho hsigma

theorem image_pivotSupplierPrimes_eq_pivotFiber
    {X L s m : ℕ} (hm : 0 < m) (hmsmall : m ≤ Nat.sqrt X / 2) :
    (pivotSupplierPrimes X L s m).image (pivotBaseOfPrime L s m) =
      pivotFiber X L s m :=
  (portfolioClaims Unit).problem249FirstHarmonicPivotFiber hm hmsmall

theorem supplierPrime_not_globally_isolated_counterexample :
    pivotOffset 20 1 = 20 ∧
      18 ∈ pivotFiber 16 20 1 2 ∧
      pivotPrime 18 20 1 = 19 ∧
      19 ∣ pivotArgument 18 20 1 ∧
      19 ∣ 18 + 1 :=
  (portfolioClaims Unit).problem249FirstHarmonicPivotIsolationCounterexample

theorem windowFirstExp_sum_eq_pivot_decomposition
    (h X L s : ℕ) (η : ℝ) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L) =
      pivotCenteredCorrelation h X L s η +
      pivotFiberMeanContribution h X L s η +
      pivotBadContribution h X L s η +
      pivotNonSupplierContribution h X L s :=
  (portfolioClaims Unit).problem249FirstHarmonicPivotDecomposition h X L s η

theorem first_harmonic_gap_of_pivotBudgetAt
    {h X L s : ℕ} {η : ℝ} (hbudget : PivotBudgetAt h X L s η) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤
      (9 / 10 : ℝ) * X :=
  (portfolioClaims Unit).problem249FirstHarmonicPivotBudget hbudget

theorem irrational_totient_series_of_pivotResidualDecorrelation
    (hmix : DTWPivotResidualDecorrelation) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  (portfolioClaims Unit).problem249FirstHarmonicPivotResidualDecorrelation hmix

theorem actualLcmTailDiff_shift_pos
    {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 <
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J) :=
  (portfolioClaims Unit).problem249ActualLcmPositiveCorridor ha hshort

theorem actualLcm_trueEndpointSurvivor_neg
    {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a) {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J)) :
    -carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) d K < 0 ∧
      endpointSurvivor (periodLcm (2 ^ a))
        (periodLcm (2 ^ a) + J) K
        (-carryOrbit (periodLcm (2 ^ a))
          (periodLcm (2 ^ a) + J) d K) :=
  (portfolioClaims Unit).problem249ActualLcmTrueEndpointSurvivor ha hshort hd

theorem actualLcm_integral_forces_topEdgeResidue
    {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a) {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J))
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
      (2 : ℤ) ^ K) :
    let H := periodLcm (2 ^ a)
    let e := carryOrbit H (H + J) d K
    let P := (2 : ℤ) ^ K
    let B := ((2 * H + J + K + 2 : ℕ) : ℤ)
    windowDiscrepancy H (H + J) K % P = P - e ∧
      P - B < windowDiscrepancy H (H + J) K % P ∧
      windowDiscrepancy H (H + J) K % P < P :=
  (portfolioClaims Unit).problem249ActualLcmTopEdgeResidue ha hshort hd hroom

theorem scaleFullTarget_miss_of_projected_separation
    {H D : ℕ} (hcontrol : ControlledForeignProjection H D)
    (hseparation : ProjectedFullTargetSeparation H D) :
    ¬ScaleFullTargetHit H :=
  (portfolioClaims Unit).problem249ActualForeignResidueProjection.2.2
    hcontrol hseparation

theorem irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses :
    Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m :=
  (portfolioClaims Unit).problem68

theorem irrational_factorialGapSeries_iff_cofinal_nonunit_carries :
    Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ factorialGapStepCarry m ≠ 1 :=
  (portfolioClaims Unit).problem68Carry

theorem no_cofinallyBoundedNegative_of_normalizedVanishes
    (a C D magnitude : ℕ → ℕ) (B : ℕ)
    (hB : 0 < B) (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hRise : ∀ n, C (n + 1) ≤ C n + B)
    (hmagnitude : ∀ n, 0 < magnitude n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * magnitude n < C n)
    (hnegative : ∀ n, ∃ t e, n ≤ t ∧ 0 < e ∧ e ≤ B ∧
      D t + e = (a t - 1) * C t) : False :=
  (portfolioClaims Unit).problem243 a C D magnitude B hB ha hCpos hC hD hRise
    hmagnitude hvanish hnegative

theorem no_eventuallyPeriodicNegative_orbit
    (a D C e : ℕ → ℕ) (N h M : ℕ)
    (hh : 0 < h) (hM : 0 < M) (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e (N + n))
    (helt : ∀ n, e (N + n) < a (N + n))
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (N + n + h) = e (N + n))
    (hphase : ∀ n, C (N + n + h) = C (N + n) + M) : False :=
  (portfolioClaims Unit).problem243Periodic a D C e N h M hh hM ha hepos helt
    hD hC hshape hperiod hphase

theorem boundedNegativePart_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (B : ℕ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (hbound : ∀ n, -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  simpa [centeredState, ErdosProblems.Erdos243.centeredState] using
    ErdosProblems.Erdos243.boundedNegativePart_eventually_zero
      a C D E B ha hCpos hC hD hE hcentered hbound hvanish

theorem sylvesterNext_eventually_of_summable_negativeRelativeMass
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, C (n + 1) = nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) =
      (C n : ℤ) - centeredState (a n) (D n) (C n))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n)
    (hsum : Summable
      (negativeRelativeMass C
        (fun n ↦ centeredState (a n) (D n) (C n)))) :
    ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  simpa [negativeRelativeMass, sylvesterNext, nextDenState, nextTailState,
    centeredState, ErdosProblems.Erdos243.negativeRelativeMass,
    ErdosProblems.Erdos243.sylvesterNext,
    ErdosProblems.Erdos243.nextDenState,
    ErdosProblems.Erdos243.nextTailState,
    ErdosProblems.Erdos243.centeredState] using
    ErdosProblems.Erdos243.sylvesterNext_eventually_of_summable_negativeRelativeMass
      a D C hD hC hCpos hstep hvanish hsum

theorem finrank_totientKernelThroughLevelFamily_eq (e : ℕ) (he : 1 ≤ e) :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 := by
  simpa [totientKernelThroughLevelFamily, totientKernelSeq,
    Erdos249257.totientKernelThroughLevelFamily,
    Erdos249257.totientKernelSeq] using
    Erdos249257.finrank_totientKernelThroughLevelFamily_eq e he

theorem not_finiteDimensional_span_fullTotientKernel :
    ¬ FiniteDimensional ℚ
      (Submodule.span ℚ (Set.range fullTotientKernelFamily)) := by
  simpa [fullTotientKernelFamily, totientKernelSeq,
    Erdos249257.fullTotientKernelFamily,
    Erdos249257.totientKernelSeq] using
    Erdos249257.not_finiteDimensional_span_fullTotientKernel

theorem exists_totientDyadicSectionBasis :
    Nonempty
      (Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily))) :=
  (portfolioClaims Unit).problem249Basis

theorem finrank_allBaseTotientKernelThroughLevelFamily_eq_of_linearIndependent
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (hcanon : LinearIndependent ℚ (canonicalAllBaseTotientKernelFamily k e)) :
    finrank ℚ
      (Submodule.span ℚ
        (Set.range (allBaseTotientKernelThroughLevelFamily k e))) =
      k ^ e + 1 := by
  simpa using (portfolioClaims Unit).problem249AllBaseRank k e hk he hcanon

theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1 :=
  (portfolioClaims Unit).problem249VisibleCoprimeMass

theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ)) :=
  (portfolioClaims Unit).problem249SquaredGcdMoment

theorem runHeight_defect_fib_sum_lower (e : List ℕ) :
    Nat.fib (e.length + 3) + Nat.fib (e.length + 1) * e.sum ≤
      runHeight (defectRunLengths e) :=
  (portfolioClaims Unit).problem249SternBrocotRunStability e

theorem cylinderMass_split (a b : ℕ+) :
    cylinderMass a b =
      1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + cylinderMass (a + b) b + cylinderMass a (a + b) :=
  (portfolioClaims Unit).problem249CylinderMassSplit a b

theorem lcm_factorIdeal_finiteRank_shiftAlgebra_not_sufficient
    (t : ℕ) (ht : 3 ≤ t) :
    ∃ c a : ℕ → ℤ,
      (∃ k, c k ≠ 0) ∧
      (∀ i, a i = dyadicCoboundary c i) ∧
      ∀ terms : List (ℕ × ℤ),
        ∃ d b : ℕ → ℤ,
          (∀ i, d i = shiftLinearCombination terms c i) ∧
          (∀ i, b i = shiftLinearCombination terms a i) ∧
          (∀ i, b i = dyadicCoboundary d i) ∧
          (∀ n L, dyadicClearedPrefix b n L =
            (2 : ℤ) ^ L * d n - d (n + L)) ∧
          (∀ i, (Nat.totient (periodLcm t) : ℤ) ∣ b i) ∧
          (∀ j, j ∣ periodLcm t → ∀ i, (Nat.totient j : ℤ) ∣ b i) ∧
          (∀ i, |d i| ≤ shiftLinearWeight terms *
            |(Nat.totient (periodLcm t) : ℤ)|) ∧
          ∀ i, |b i| ≤ shiftLinearWeight terms *
            (2 * |(Nat.totient (periodLcm t) : ℤ)|) := by
  simpa only [dyadicCoboundary,
    Erdos249257.TotientTailPeriodKiller.dyadicCoboundary,
    periodLcm_eq_source, dyadicClearedPrefix_eq_source,
    shiftLinearCombination_eq_source, shiftLinearWeight_eq_source] using
    Erdos249257.TotientTailPeriodKiller.lcm_factorIdeal_finiteRank_shiftAlgebra_not_sufficient
      t ht

theorem volume_mersenneAchievementSet : volume mersenneAchievementSet = 1 := by
  simpa [mersenneAchievementSet, positiveMersenneSupportValue, mersenneWeight,
    Erdos249257.mersenneAchievementSet,
    Erdos249257.positiveMersenneSupportValue,
    Erdos249257.mersenneWeight] using
    Erdos249257.volume_mersenneAchievementSet

theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  simpa using Erdos249257.irrational_erdosSum_full_support b hb

theorem irrational_erdosSupportSeries_pairwise_coprime
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    Irrational (erdosSupportSeries b A) := by
  simpa [erdosSupportSeries, Erdos249257.erdosSupportSeries] using
    Erdos249257.irrational_erdosSupportSeries_pairwise_coprime
      b A hb hA hpair hsum

theorem irrational_ratWeightSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (γ : ℕ → ℚ) (hb : 2 ≤ b) (hm : 0 < m)
    (hγ0 : ∀ n : ℕ, 0 ≤ γ n)
    (hper : ∀ n : ℕ, N₀ ≤ n → γ (n + m) = γ n)
    (hpos : ∃ a : ℕ, N₀ ≤ a ∧ 0 < a ∧ 0 < γ a) :
    Irrational (∑' a : ℕ, ((γ a : ℝ)) / ((b : ℝ) ^ a - 1)) := by
  simpa using
    Erdos249257.irrational_ratWeightSeries_eventuallyPeriodic
      b m N₀ γ hb hm hγ0 hper hpos

theorem irrational_erdosSupportSeries_of_orthogonalPetalBouquet
    {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (hselection : SunflowerForcedSlotTailSelection A) :
    Irrational (erdosSupportSeries 2 A) := by
  have hB' := orthogonalPetalBouquet_to_source hB
  have hselection' := sunflowerForcedSlotTailSelection_to_source hselection
  simpa [erdosSupportSeries, Erdos249257.erdosSupportSeries] using
    Erdos249257.SupportSunflowerDichotomy.irrational_erdosSupportSeries_of_orthogonalPetalBouquet
      hB' hselection'

theorem finite_period_noncollapse_rat_den_interface
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b (finiteErdosSum F b).den) :
    orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id :=
  (portfolioClaims Unit).problem257FinitePeriod F b hF h0 hb hcop

theorem volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0) :=
  (portfolioClaims Unit).problem257Dichotomy J

theorem exists_shifted_odd_tail_nat_states_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) := by
  simpa [supportCoeff, erdosSupportSeries, binaryCoeffTail,
    Erdos249257.supportCoeff, Erdos249257.erdosSupportSeries,
    Erdos249257.binaryCoeffTail] using
    Erdos249257.exists_shifted_odd_tail_nat_states_of_support_fraction
      A hA p c v hv hvalue

theorem supportCoeff_mul_eq_add_defect
    (A : Set ℕ) {a x : ℕ} (ha : a ∈ A) (ha0 : 0 < a) (hx0 : 0 < x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x := by
  simpa [supportCoeff, compositeDilationDefect,
    Erdos249257.supportCoeff,
    Erdos249257.CompositeDilationDefect.compositeDilationDefect] using
    Erdos249257.CompositeDilationDefect.supportCoeff_mul_eq_add_defect
      A ha ha0 hx0

theorem seven_le_of_intBand_odd {p D q : ℤ}
    (hp : 0 < p) (hD : 0 < D) (hq : 0 < q)
    (hpodd : Odd p) (hDodd : Odd D) (hqodd : Odd q)
    (hband : IntBand p D q) :
    7 ≤ p := by
  simpa [IntBand, Erdos249257.HalfGreedyTwoThirdsBand.IntBand] using
    Erdos249257.HalfGreedyTwoThirdsBand.seven_le_of_intBand_odd
      hp hD hq hpodd hDodd hqodd hband

theorem exists_primeGap0_gt (M : ℕ) : ∃ n, M < primeGap0 n :=
  (portfolioClaims Unit).problem251 M

theorem coefficientOnlyNoGo : CoefficientOnlyNoGo := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [carryPartialSum, carryCoeff,
      ErdosProblems.Erdos251.carryPartialSum,
      ErdosProblems.Erdos251.carryCoeff] using
      ErdosProblems.Erdos251.carryPartialSum_natCast_eq n
  · intro h hpos
    simpa [carryCoeff, ErdosProblems.Erdos251.carryCoeff] using
      ErdosProblems.Erdos251.carryCoeff_natCast_not_eventually_periodic hpos
  · intro h hpos
    simpa [primeGap0, prime0, ErdosProblems.Erdos251.primeGap0,
      ErdosProblems.Erdos251.prime0] using
      ErdosProblems.Erdos251.primeGap0_not_eventually_periodic hpos

theorem primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch
    {T : ℕ → ℚ} (h : ℕ)
    (hrec : DyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) T)
    (hsupply : ∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      primeGap0 (N + h + 1) ≠ primeGap0 (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) :=
  (portfolioClaims Unit).problem251CofinalSmallMismatch h hrec hsupply

theorem irrational_tsum_primeDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  (portfolioClaims Unit).problem251Equivalence hprime

theorem kernel_235_minor_eq_neg_one_fifteen :
    threePrimeKernelQ 2 3 5 0 0 0 *
          threePrimeKernelQ 2 3 5 1 1 0 -
        threePrimeKernelQ 2 3 5 1 0 0 *
          threePrimeKernelQ 2 3 5 0 1 0 =
      -(1 / 15 : ℚ) :=
  (portfolioClaims Unit).problem269

theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x :=
  (portfolioClaims Unit).problem269Lcm hp hq hr hpq hpr hqr hx

theorem carry_eq_residueDigit_add_coboundary
    (B : ℤ) (hB : 0 < B)
    (base carry digit : ℕ → ℤ)
    (hrec : ∀ n,
      carry (n + 1) = base n * carry n - B * digit n) :
    let residue := fun n => weightedCarryResidue B (carry n)
    let quotient := fun n => weightedCarryQuotient B (carry n)
    ∀ n,
      digit n =
        weightedResidueDigit B (base n)
          (residue n) (residue (n + 1)) +
        base n * quotient n - quotient (n + 1) := by
  simpa [weightedCarryResidue, weightedCarryQuotient,
    weightedResidueDigit, ErdosProblems.Erdos269.carryResidue,
    ErdosProblems.Erdos269.carryQuotient,
    ErdosProblems.Erdos269.residueDigit] using
    ErdosProblems.Erdos269.carry_eq_residueDigit_add_coboundary
      B hB base carry digit hrec

theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False := by
  have hescape' :
      ErdosProblems.Erdos269.CofinalLocalWindowEscape b m shortBound := by
    simpa only [CofinalLocalWindowEscape,
      ErdosProblems.Erdos269.CofinalLocalWindowEscape,
      conditionalWindowBase_eq_source,
      conditionalWindowForcing_eq_source,
      conditionalLeastPositiveResidue_eq_source] using hescape
  simpa using
    ErdosProblems.Erdos269.no_positive_reducedCarry_of_cofinalLocalWindowEscape
      b m shortBound hescape' B hBpos hBcoprime d hrec hpos hbound

theorem exists_small_translation_separating_arguments
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      ∀ i j, i ≠ j →
        ¬ SamePositiveRay (c i + shift) (c j + shift) :=
  (portfolioClaims ι).problem1041 c hc hε

theorem constant_perturbation_roots_in_unitDisk
    (f : Polynomial ℂ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hroots : ∀ b ∈ f.roots, ‖b‖ ≤ ρ) (hε : 0 < ε)
    (hmargin : ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1)
    {shift : ℂ} (hshift : ‖shift‖ < ε) :
    ∀ a : ℂ, (f + Polynomial.C shift).eval a = 0 → ‖a‖ < 1 :=
  (portfolioClaims Unit).problem1041Roots f hf hdeg hsplit hρ hroots hε
    hmargin hshift

theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit :=
  (portfolioClaims Unit).problem1049 hN hK

theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) :=
  (portfolioClaims Unit).problem1049Recurrence hr N

theorem tailOrbitBlockGap_of_nonpositiveBlockDensity
    (hdensity : TotientTailOrbitNonpositiveBlockDensity) :
    TotientTailOrbitBlockGap := by
  exact TotientTailOrbitBlockGap_eq_source.mpr
    (ErdosProblems.Erdos249.tailOrbitBlockGap_of_nonpositiveBlockDensity
      (TotientTailOrbitNonpositiveBlockDensity_eq_source.mp hdensity))

theorem irrational_totient_series_of_tailOrbitBlockGap
    (hgap : TotientTailOrbitBlockGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact ErdosProblems.Erdos249.irrational_totient_series_of_tailOrbitBlockGap
    (TotientTailOrbitBlockGap_eq_source.mp hgap)

theorem irrational_totient_series_of_naturalPrimeTailOrbitStrictGap
    (hgap : DTWNaturalPrimeTailOrbitStrictGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact ErdosProblems.Erdos249.irrational_totient_series_of_naturalPrimeTailOrbitStrictGap
    (DTWNaturalPrimeTailOrbitStrictGap_eq_source.mp hgap)

end Erdos249257.ExternalVerification
