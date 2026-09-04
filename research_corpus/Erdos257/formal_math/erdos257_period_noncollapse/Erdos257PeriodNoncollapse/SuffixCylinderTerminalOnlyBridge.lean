import Erdos257PeriodNoncollapse.SuffixCylinderStage51
import Erdos257PeriodNoncollapse.SuffixCylinderGlobalProducer
import Erdos257PeriodNoncollapse.SuffixCylinderProfiledSwallow
import Erdos257PeriodNoncollapse.TerminalOnlyCofinal

/-!
# Suffix-cylinder stages feed the terminal-only half consumer

The suffix-cylinder construction carries substantially more information than
the terminal-only compactness-free consumer needs.  This module records the
lossy projection explicitly: one selected representative already gives a
normalized terminal strip witness.  At a feedback row the same conclusion
survives both outputs of the total feedback theorem, because a localized
one-hole seam always realizes at least one of carries `3` and `4`.
-/

namespace Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCarryReachability
open Erdos257PeriodNoncollapse.HalfCarrySelectedWindow
open Erdos257PeriodNoncollapse.FixedCoeffRewind
open Erdos257PeriodNoncollapse.SuffixCylinderThreshold
open Erdos257PeriodNoncollapse.SuffixCylinderGlobalProducer
open Erdos257PeriodNoncollapse.SuffixCylinderStage51
open Erdos257PeriodNoncollapse.SuffixCylinderInStrip
open Erdos257PeriodNoncollapse.SuffixCylinderProfiledGap
open Erdos257PeriodNoncollapse.SuffixCylinderProfiledSwallow

/-- Every all-prefix reachable terminal state is, after forgetting its
history, a terminal-only strip witness. -/
theorem halfTerminalOnlyStripWitness_of_halfTerminalReachable
    {N k : ℕ} (hreach : HalfTerminalReachable N k) :
    HalfTerminalOnlyStripWitness N := by
  obtain ⟨a, ha, _hterminal⟩ := hreach
  refine ⟨a, ha.1, ha.2.1, ?_⟩
  by_cases hN : N = 0
  · subst N
    simp [integerHalfCarry_zero, halfStripBound]
  · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hstrip := ha.2.2 N hNpos le_rfl
    have hnonnegZ :
        (0 : ℤ) ≤ integerHalfCarry (wordSupport a) (N - 1) := by
      omega
    have hnonnegR :
        (0 : ℝ) ≤ (integerHalfCarry (wordSupport a) (N - 1) : ℝ) := by
      exact_mod_cast hnonnegZ
    rw [abs_of_nonneg hnonnegR]
    exact_mod_cast hstrip.2

/-- A nonempty selected window contains a terminal-only witness: choose its
representative with terminal carry `1`. -/
theorem SelectedHalfWindow.halfTerminalOnlyStripWitness
    {N R : ℕ} (W : SelectedHalfWindow N R) (hR : 1 ≤ R) :
    HalfTerminalOnlyStripWitness N := by
  apply halfTerminalOnlyStripWitness_of_halfTerminalReachable
  exact ⟨W.word 1 (by omega) hR,
    W.admissible 1 (by omega) hR,
    W.terminal 1 (by omega) hR⟩

/-- Forgetting the endpoint and cylinder data of a full cylinder stage leaves
a terminal-only witness at the same depth. -/
theorem CylinderStage.halfTerminalOnlyStripWitness
    {K N : ℕ} (S : CylinderStage K N) :
    HalfTerminalOnlyStripWitness N := by
  apply
    Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.SelectedHalfWindow.halfTerminalOnlyStripWitness
      S.window
  unfold halfStripBound
  omega

/-- A realized localized seam still gives a terminal-only witness.  The seam
can delete at most one carry, so one of `3` and `4` survives. -/
theorem halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt
    {N : ℕ} {delta c : ℤ}
    (hrealize : ProtectedEvenSeamRealizedAt N delta c) :
    HalfTerminalOnlyStripWitness N := by
  let k : ℕ := if 2 * delta - c = 3 then 4 else 3
  have hk3 : 3 ≤ k := by
    simp only [k]
    split_ifs <;> omega
  have hk27 : k ≤ 27 := by
    simp only [k]
    split_ifs <;> omega
  have hnotHole : (k : ℤ) ≠ 2 * delta - c := by
    simp only [k]
    split_ifs <;> omega
  have hseam : EvenSeamReachable delta c k :=
    (evenSeamReachable_iff delta c k).2 hnotHole
  exact halfTerminalOnlyStripWitness_of_halfTerminalReachable
    (hrealize k hk3 hk27 hseam)

/-- A two-sheet stage always contains a terminal-only witness.  Its sole
missing carry cannot delete both `1` and `2`, and both lie in every half
strip.  This consumes the operational in-strip object directly, without
projecting through the legacy protected `3..27` interface. -/
theorem InStripTwoSheetStage.halfTerminalOnlyStripWitness
    {K N : ℕ} (T : InStripTwoSheetStage K N) :
    HalfTerminalOnlyStripWitness N := by
  let q : ℕ := if T.hole = 1 then 2 else 1
  have hq : 1 ≤ q := by
    simp only [q]
    split_ifs <;> omega
  have hqB : q ≤ halfStripBound N := by
    simp only [q]
    split_ifs <;> unfold halfStripBound <;> omega
  have hqHole : q ≠ T.hole := by
    simp only [q]
    split_ifs with hhole <;> omega
  apply halfTerminalOnlyStripWitness_of_halfTerminalReachable
  exact T.halfTerminalReachable_of_ne_hole hq hqB hqHole

/-- **Operational feedback-row terminal consumer.**  The exact two-output
feedback theorem already gives a terminal-only witness at the next row:
either the full cylinder advances, or the retained two sheets contain one of
the carries `1` and `2`.  In particular no lower bound such as
`27 ≤ halfStripBound (N + 1)` is needed. -/
theorem CylinderStage.halfTerminalOnlyStripWitness_after_operational_feedback
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    HalfTerminalOnlyStripWitness (N + 1) := by
  rcases
      Erdos257PeriodNoncollapse.SuffixCylinderInStrip.CylinderStage.feedbackAdvance_or_inStripTwoSheet
        S hN hK1N hrow with
    hstage | htwoSheet
  · rcases hstage with ⟨S'⟩
    exact
      Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
        S'
  · rcases htwoSheet with ⟨T⟩
    exact
      Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.InStripTwoSheetStage.halfTerminalOnlyStripWitness
        T

/-- **Feedback-row terminal consumer.**  At an exact half-divisor horizon,
the total suffix-cylinder feedback theorem produces a terminal-only witness
at the next row in both cases: either the full cylinder advances, or its
localized one-hole seam supplies a surviving terminal state. -/
theorem CylinderStage.halfTerminalOnlyStripWitness_after_feedback
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1))
    (h27 : 27 ≤ halfStripBound (N + 1)) :
    HalfTerminalOnlyStripWitness (N + 1) := by
  rcases
      Erdos257PeriodNoncollapse.SuffixCylinderGlobalProducer.CylinderStage.feedbackStep_or_protectedSeam
        S hN hK1N hrow h27 with
    hstage | hseam
  · rcases hstage with ⟨S'⟩
    exact
      Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
        S'
  · obtain ⟨delta, c, hrealize⟩ := hseam
    exact halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt hrealize

/-- A surviving canonical parent in either sheet of a profiled finite gap
produces an actual admissible successor word.  This is the proof-bearing
consumer missing from the arithmetic-only `TrackedParentSurvives` socket. -/
theorem ProfiledGapStage.halfTerminalOnlyStripWitness_after_trackedParentSurvives
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hN : 1 ≤ N) (hready : T.Ready)
    (hsurvive : profiledGapStageTrackedNextParentSurvives T
      (supportCoeff (wordSupport T.lowerPrefix) (N + 1))
      (supportCoeff (wordSupport T.upperPrefix) (N + 1))) :
    HalfTerminalOnlyStripWitness (N + 1) := by
  let lowerCoeff := supportCoeff (wordSupport T.lowerPrefix) (N + 1)
  let upperCoeff := supportCoeff (wordSupport T.upperPrefix) (N + 1)
  have hprofile : T.HasNextCoeffProfile lowerCoeff upperCoeff := by
    simpa [lowerCoeff, upperCoeff] using T.hasNextCoeffProfile_of_ready hready
  have hsurvive' :
      TrackedParentSurvives T.gapLo T.gapHi (halfStripBound N)
        lowerCoeff upperCoeff (halfStripBound (N + 1)) := by
    simpa [profiledGapStageTrackedNextParentSurvives, lowerCoeff, upperCoeff]
      using hsurvive
  rcases hsurvive' with hlower | hupper
  · obtain ⟨q, hq, hqB, hparent⟩ := hlower
    let p := parent lowerCoeff q
    have hp : 1 ≤ p := explicitParent_pos hq
    have hpR : p ≤ T.gapLo - 1 := by
      dsimp [p]
      omega
    let beta : Bool := decide (explicitParentBitZ lowerCoeff q = 1)
    have hqrec : (q : ℤ) = 2 * (p : ℤ) - (lowerCoeff : ℤ) -
        (if beta then 1 else 0) := by
      have hrec := explicitParent_recurrence lowerCoeff q
      rcases explicitParentBitZ_zero_or_one lowerCoeff q with hb | hb
      · simpa [p, beta, hb] using hrec
      · simpa [p, beta, hb] using hrec
    apply halfTerminalOnlyStripWitness_of_halfTerminalReachable
    exact halfTerminalReachable_succ_of_admissibleParent hN
      (T.lower.word p hp hpR) (T.lower.admissible p hp hpR)
      (T.lower.terminal p hp hpR) (hprofile.1 p hp hpR) beta hqrec
      hq hqB
  · obtain ⟨q, hq, hqB, hparentLo, hparentHi⟩ := hupper
    let p := parent upperCoeff q
    have hpL : T.gapHi + 1 ≤ p := by
      dsimp [p]
      omega
    have hpR : p ≤ halfStripBound N := by
      simpa [p] using hparentHi
    let beta : Bool := decide (explicitParentBitZ upperCoeff q = 1)
    have hqrec : (q : ℤ) = 2 * (p : ℤ) - (upperCoeff : ℤ) -
        (if beta then 1 else 0) := by
      have hrec := explicitParent_recurrence upperCoeff q
      rcases explicitParentBitZ_zero_or_one upperCoeff q with hb | hb
      · simpa [p, beta, hb] using hrec
      · simpa [p, beta, hb] using hrec
    apply halfTerminalOnlyStripWitness_of_halfTerminalReachable
    exact halfTerminalReachable_succ_of_admissibleParent hN
      (T.upper.word p hpL hpR) (T.upper.admissible p hpL hpR)
      (T.upper.terminal p hpL hpR) (hprofile.2 p hpL hpR) beta hqrec
      hq hqB

/-- In particular, a binary-adjacent singleton gap can never kill the next
terminal-only strip witness. -/
theorem ProfiledGapStage.halfTerminalOnlyStripWitness_after_singletonGap
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hN : 1 ≤ N) (hready : T.Ready)
    (hadjacent : T.HasAdjacentPrefixes)
    (hsingleton : T.gapLo = T.gapHi) :
    HalfTerminalOnlyStripWitness (N + 1) := by
  apply ProfiledGapStage.halfTerminalOnlyStripWitness_after_trackedParentSurvives
    T hN hready
  exact
    Erdos257PeriodNoncollapse.SuffixCylinderProfiledSwallow.ProfiledGapStage.trackedNextParentSurvives_of_singletonGap
      T hadjacent hsingleton

/-- The certified depth-51 cylinder already yields a concrete normalized
terminal strip witness. -/
theorem fullCylinderStage51_halfTerminalOnlyStripWitness :
    HalfTerminalOnlyStripWitness 51 :=
  Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
    fullCylinderStage51

/-- The explicitly promoted second-feedback successor gives the next
concrete terminal strip witness as well. -/
theorem fullCylinderStage52_halfTerminalOnlyStripWitness :
    HalfTerminalOnlyStripWitness 52 :=
  Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
    fullCylinderStage52

/-- The certified stage at row `52` advances ordinarily through the last row
before the next feedback boundary. -/
noncomputable def fullCylinderStage53 : FullCylinderStage 26 53 :=
  fullCylinderStage52.advance (by norm_num) (by norm_num)

/-- The ordinary successor of the certified row-`52` stage supplies the
next concrete terminal-only witness. -/
theorem fullCylinderStage53_halfTerminalOnlyStripWitness :
    HalfTerminalOnlyStripWitness 53 :=
  Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
    fullCylinderStage53

/-- At the row-`54` feedback boundary, both exact outputs of the operational
fan-in carry a terminal-only witness. -/
theorem fullCylinderStage54_halfTerminalOnlyStripWitness :
    HalfTerminalOnlyStripWitness 54 :=
  Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness_after_operational_feedback
    fullCylinderStage53 (by norm_num) (by norm_num) (by norm_num)

/-- One row beyond the row-`54` feedback boundary still has an unconditional
terminal-only witness.  A full-cylinder output advances ordinarily.  An
in-strip two-sheet output is a binary-adjacent singleton profiled gap, so its
surviving canonical parent supplies the row-`55` witness. -/
theorem fullCylinderStage55_halfTerminalOnlyStripWitness :
    HalfTerminalOnlyStripWitness 55 := by
  rcases
      Erdos257PeriodNoncollapse.SuffixCylinderInStrip.CylinderStage.feedbackAdvance_or_inStripTwoSheet
        fullCylinderStage53 (by norm_num) (by norm_num) (by norm_num) with
    hstage | htwoSheet
  · rcases hstage with ⟨S⟩
    exact
      Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
        (S.advance (by norm_num) (by norm_num))
  · rcases htwoSheet with ⟨T⟩
    let P :=
      Erdos257PeriodNoncollapse.SuffixCylinderProfiledGap.profiledGapStageOfTwoSheet T
    apply
      Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.ProfiledGapStage.halfTerminalOnlyStripWitness_after_singletonGap
        P (by norm_num) (by norm_num)
    · exact
        Erdos257PeriodNoncollapse.SuffixCylinderProfiledAdjacency.profiledGapStageOfTwoSheet_hasAdjacentPrefixes
          T
    · rfl

/-- Cofinal full-cylinder stages imply the strictly weaker terminal-only
cofinal producer expected by the closed achievement-set consumer. -/
theorem cofinalTerminalOnlyStrip_of_cofinalCylinderStages
    (hstages : ∀ N : ℕ, ∃ M K : ℕ,
      max N 1 ≤ M ∧ Nonempty (CylinderStage K M)) :
    HalfCarryCofinalTerminalOnlyStrip := by
  intro N
  obtain ⟨M, K, hNM, hstage⟩ := hstages N
  rcases hstage with ⟨S⟩
  exact ⟨M, hNM,
    Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge.CylinderStage.halfTerminalOnlyStripWitness
      S⟩

/-- Direct end-to-end consumer: cofinal suffix-cylinder stages produce an
infinite support whose Mersenne support series is the rational value `1/2`. -/
theorem exists_infinite_support_half_of_cofinalCylinderStages
    (hstages : ∀ N : ℕ, ∃ M K : ℕ,
      max N 1 ≤ M ∧ Nonempty (CylinderStage K M)) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_cofinalTerminalOnlyStrip
    (cofinalTerminalOnlyStrip_of_cofinalCylinderStages hstages)

#print axioms halfTerminalOnlyStripWitness_of_halfTerminalReachable
#print axioms SelectedHalfWindow.halfTerminalOnlyStripWitness
#print axioms CylinderStage.halfTerminalOnlyStripWitness
#print axioms halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt
#print axioms InStripTwoSheetStage.halfTerminalOnlyStripWitness
#print axioms CylinderStage.halfTerminalOnlyStripWitness_after_operational_feedback
#print axioms CylinderStage.halfTerminalOnlyStripWitness_after_feedback
#print axioms ProfiledGapStage.halfTerminalOnlyStripWitness_after_trackedParentSurvives
#print axioms ProfiledGapStage.halfTerminalOnlyStripWitness_after_singletonGap
#print axioms fullCylinderStage51_halfTerminalOnlyStripWitness
#print axioms fullCylinderStage52_halfTerminalOnlyStripWitness
#print axioms fullCylinderStage53
#print axioms fullCylinderStage53_halfTerminalOnlyStripWitness
#print axioms fullCylinderStage54_halfTerminalOnlyStripWitness
#print axioms fullCylinderStage55_halfTerminalOnlyStripWitness
#print axioms cofinalTerminalOnlyStrip_of_cofinalCylinderStages
#print axioms exists_infinite_support_half_of_cofinalCylinderStages

end Erdos257PeriodNoncollapse.SuffixCylinderTerminalOnlyBridge
