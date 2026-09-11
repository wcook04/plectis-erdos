import Erdos249257.SuffixCylinderFiniteGap

/-!
# Cutoff-profiled continuation of a finite suffix-cylinder gap

The first finite-gap state remembers two complementary children of one
boundary prefix.  That shape is enough for the immediately following odd
coefficient row, but it is not stable under another cutoff promotion: the
two live sheets acquire independent longer prefixes.  This module records
those prefixes directly.  Consequently every row covered by the current
cutoff has an exact per-sheet coefficient profile, with no cross-sheet
coefficient-equality assumption.
-/

namespace Erdos249257.SuffixCylinderProfiledGap

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderInStrip
open Erdos249257.SuffixCylinderFiniteGap

/-- A finite carry gap together with independent literal prefixes for its
two live suffix-cylinder sheets.  The parameter `M` is the actual retained
cutoff, rather than the predecessor of that cutoff.

The endpoint-separation field is the invariant needed to promote the upper
sheet when the cutoff reaches its next feedback boundary. -/
structure ProfiledGapStage (M N : ℕ) where
  hMN : M ≤ N
  gapLo : ℕ
  gapHi : ℕ
  gapLo_pos : 1 ≤ gapLo
  gap_order : gapLo ≤ gapHi
  gapHi_le : gapHi ≤ halfStripBound N
  lowerPrefix : HalfWord M
  lower : SelectedHalfWindow N (gapLo - 1)
  lowerCylinder : HasSuffixCylinderAt lower hMN (gapLo - 1)
  lowerLiteral : ∀ q (hq : 1 ≤ q) (hqR : q ≤ gapLo - 1),
    restrictWord hMN (lower.word q hq hqR) = lowerPrefix
  upperPrefix : HalfWord M
  upperEndpoint : ℕ
  upper : SelectedHalfInterval N (gapHi + 1) (halfStripBound N)
  upperCylinder : HasSuffixCylinderOnInterval upper hMN upperEndpoint
  upperLiteral : ∀ q (hqL : gapHi + 1 ≤ q)
      (hqU : q ≤ halfStripBound N),
    restrictWord hMN (upper.word q hqL hqU) = upperPrefix
  upperCovers : halfStripBound N ≤ upperEndpoint
  endpointSeparation : upperEndpoint = gapHi + 2 ^ (N - M)

/-- The exact one-hole feedback state is the initial profiled finite-gap
state.  Its two cutoff prefixes are the marked true/false children retained
by `InStripTwoSheetStage`. -/
noncomputable def profiledGapStageOfTwoSheet
    {K N : ℕ} (T : InStripTwoSheetStage K N) :
    ProfiledGapStage (K + 1) N where
  hMN := T.hK1N
  gapLo := T.hole
  gapHi := T.hole
  gapLo_pos := T.hole_pos
  gap_order := le_rfl
  gapHi_le := T.hole_le
  lowerPrefix := extendHalfWord T.boundaryPrefix true
  lower := T.lower
  lowerCylinder := T.lowerCylinder
  lowerLiteral := T.lowerLiteral
  upperPrefix := extendHalfWord T.boundaryPrefix false
  upperEndpoint := T.upperEndpoint
  upper := T.upper
  upperCylinder := T.upperCylinder
  upperLiteral := T.upperLiteral
  upperCovers := T.upperCovers
  endpointSeparation := T.endpointSeparation

/-- Per-sheet constant coefficients at the next row.  Equality between the
two constants is intentionally not part of this interface. -/
def ProfiledGapStage.HasNextCoeffProfile
    {M N : ℕ} (T : ProfiledGapStage M N) (lowerCoeff upperCoeff : ℕ) :
    Prop :=
  (∀ q (hq : 1 ≤ q) (hqR : q ≤ T.gapLo - 1),
    supportCoeff (wordSupport (T.lower.word q hq hqR)) (N + 1) =
      lowerCoeff) ∧
  (∀ q (hqL : T.gapHi + 1 ≤ q) (hqU : q ≤ halfStripBound N),
    supportCoeff (wordSupport (T.upper.word q hqL hqU)) (N + 1) =
      upperCoeff)

/-- The current cutoff can read the next coefficient row whenever the word
depth has not passed its doubled feedback boundary. -/
def ProfiledGapStage.Ready
    {M N : ℕ} (_T : ProfiledGapStage M N) : Prop :=
  N ≤ 2 * M

/-- Every ready profiled gap has an exact next-row coefficient profile,
obtained from its two retained literal prefixes.  This is the coefficient
producer needed by an iterator; it replaces the non-iterable requirement
that the two sheets have one common coefficient. -/
theorem ProfiledGapStage.hasNextCoeffProfile_of_ready
    {M N : ℕ} (T : ProfiledGapStage M N) (hready : T.Ready) :
    T.HasNextCoeffProfile
      (supportCoeff (wordSupport T.lowerPrefix) (N + 1))
      (supportCoeff (wordSupport T.upperPrefix) (N + 1)) := by
  have hMnext : M < N + 1 := T.hMN.trans_lt (Nat.lt_succ_self N)
  have hfeedback : N + 1 ≤ 2 * M + 1 := by
    exact Nat.add_le_add_right hready 1
  have hNnext : N < N + 1 := Nat.lt_succ_self N
  constructor
  · intro q hq hqR
    exact supportCoeff_word_eq_of_restrict_before_feedback (n := N + 1)
      T.hMN (T.lower.word q hq hqR) T.lowerPrefix
        (T.lowerLiteral q hq hqR) hMnext hfeedback hNnext
  · intro q hqL hqU
    exact supportCoeff_word_eq_of_restrict_before_feedback (n := N + 1)
      T.hMN (T.upper.word q hqL hqU) T.upperPrefix
        (T.upperLiteral q hqL hqU) hMnext hfeedback hNnext

/-- Structure-preserving successor with independent coefficients on the two
live sheets.  The exact child gap is
`[2*gapLo-lowerCoeff-1, 2*gapHi-upperCoeff]`; in particular, this constructor
continues to apply after cutoff promotion has made the two coefficients
different. -/
noncomputable def ProfiledGapStage.advanceOfNextCoeffProfile
    {M N lowerCoeff upperCoeff : ℕ} (T : ProfiledGapStage M N)
    (hN : 1 ≤ N)
    (hprofile : T.HasNextCoeffProfile lowerCoeff upperCoeff)
    (hchildLoPos : 1 ≤ 2 * T.gapLo - lowerCoeff - 1)
    (hupperCoeff : upperCoeff ≤ 2 * T.gapHi)
    (hchildOrder :
      2 * T.gapLo - lowerCoeff - 1 ≤ 2 * T.gapHi - upperCoeff)
    (hchildHiStrip :
      2 * T.gapHi - upperCoeff ≤ halfStripBound (N + 1))
    (hupperBuffer :
      halfStripBound (N + 1) + upperCoeff ≤ 2 * halfStripBound N) :
    ProfiledGapStage M (N + 1) := by
  let childLo := 2 * T.gapLo - lowerCoeff - 1
  let childHi := 2 * T.gapHi - upperCoeff
  have hchildOrder' : childLo ≤ childHi := by
    simpa [childLo, childHi] using hchildOrder
  have hchildHiStrip' : childHi ≤ halfStripBound (N + 1) := by
    simpa [childHi] using hchildHiStrip
  let lowerRange := childLo - 1
  have hlowerRangeEq :
      lowerRange = 2 * (T.gapLo - 1) - lowerCoeff := by
    dsimp [lowerRange, childLo]
    omega
  have hlowerStrip : lowerRange ≤ halfStripBound (N + 1) := by
    exact (Nat.pred_le childLo).trans hchildOrder' |>.trans hchildHiStrip'
  have hlowerCoeff : ∀ k : ℕ, 1 ≤ k → k ≤ T.gapLo - 1 →
      selectedRowCoeff T.lower k = lowerCoeff := by
    intro k hk hkR
    rw [selectedRowCoeff, dif_pos ⟨hk, hkR⟩]
    exact_mod_cast hprofile.1 k hk hkR
  have hlowerBuffer :
      lowerRange + lowerCoeff ≤ 2 * (T.gapLo - 1) := by
    rw [hlowerRangeEq]
    omega
  let lower' : SelectedHalfWindow (N + 1) lowerRange :=
    T.lower.stepExplicit hN hlowerStrip hlowerCoeff hlowerBuffer
  have hlowerCylinder :=
    SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
      hN T.lower T.hMN hlowerStrip hlowerCoeff hlowerBuffer
      T.lowerCylinder (le_refl (T.gapLo - 1))
  have hlowerLiteral : ∀ q (hq : 1 ≤ q) (hqR : q ≤ lowerRange),
      restrictWord (T.hMN.trans (Nat.le_succ N))
        (lower'.word q hq hqR) = T.lowerPrefix := by
    intro q hq hqR
    exact SelectedHalfWindow.stepExplicit_preserves_literalPrefix
      T.lower T.hMN T.lowerPrefix hN hlowerStrip hlowerCoeff hlowerBuffer
      T.lowerLiteral q hq hqR
  have hparentLo : ∀ q : ℕ, childHi + 1 ≤ q →
      q ≤ halfStripBound (N + 1) → T.gapHi + 1 ≤ parent upperCoeff q := by
    intro q hqL hqU
    have hrec := explicitParent_bitNat_recurrence upperCoeff q
    dsimp [childHi] at hqL
    omega
  have hparentHi : ∀ q : ℕ, childHi + 1 ≤ q →
      q ≤ halfStripBound (N + 1) →
        parent upperCoeff q ≤ halfStripBound N := by
    intro q hqL hqU
    exact explicitParent_le hqU hupperBuffer
  let upper' : SelectedHalfInterval (N + 1) (childHi + 1)
      (halfStripBound (N + 1)) :=
    selectedHalfIntervalStepExplicit hN T.upper (by omega) le_rfl
      hparentLo hparentHi hprofile.2
  have hupperCoeffEndpoint : upperCoeff ≤ 2 * T.upperEndpoint := by
    have hgapEndpoint : T.gapHi ≤ T.upperEndpoint :=
      T.gapHi_le.trans T.upperCovers
    exact hupperCoeff.trans (Nat.mul_le_mul_left 2 hgapEndpoint)
  have hupperCylinder : HasSuffixCylinderOnInterval upper'
      (T.hMN.trans (Nat.le_succ N))
      (2 * T.upperEndpoint - upperCoeff) := by
    exact selectedHalfIntervalHasSuffixCylinderOnInterval_stepExplicit
      T.upper T.hMN hN (by omega) le_rfl hparentLo hparentHi hprofile.2
      T.upperCylinder hupperCoeffEndpoint
  have hupperLiteral : ∀ q (hqL : childHi + 1 ≤ q)
      (hqU : q ≤ halfStripBound (N + 1)),
      restrictWord (T.hMN.trans (Nat.le_succ N))
        (upper'.word q hqL hqU) = T.upperPrefix := by
    intro q hqL hqU
    exact selectedHalfIntervalStepExplicit_preserves_literalPrefix
      T.upper T.hMN T.upperPrefix hN (by omega) le_rfl
      hparentLo hparentHi hprofile.2 T.upperLiteral q hqL hqU
  have hupperCovers : halfStripBound (N + 1) ≤
      2 * T.upperEndpoint - upperCoeff := by
    have hbase : halfStripBound (N + 1) + upperCoeff ≤
        2 * T.upperEndpoint :=
      hupperBuffer.trans (Nat.mul_le_mul_left 2 T.upperCovers)
    omega
  have hMN : M ≤ N := T.hMN
  have hpow : 2 ^ (N + 1 - M) = 2 * 2 ^ (N - M) := by
    rw [show N + 1 - M = (N - M) + 1 by omega, pow_succ]
    ring
  have hendpointSeparation :
      2 * T.upperEndpoint - upperCoeff = childHi + 2 ^ (N + 1 - M) := by
    rw [T.endpointSeparation, hpow]
    dsimp [childHi]
    omega
  exact {
    hMN := T.hMN.trans (Nat.le_succ N)
    gapLo := childLo
    gapHi := childHi
    gapLo_pos := by simpa [childLo] using hchildLoPos
    gap_order := hchildOrder'
    gapHi_le := hchildHiStrip'
    lowerPrefix := T.lowerPrefix
    lower := by simpa [lowerRange, childLo] using lower'
    lowerCylinder := by
      simpa [lowerRange, childLo, hlowerRangeEq] using hlowerCylinder.1
    lowerLiteral := by
      intro q hq hqR
      simpa [lowerRange, childLo] using hlowerLiteral q hq hqR
    upperPrefix := T.upperPrefix
    upperEndpoint := 2 * T.upperEndpoint - upperCoeff
    upper := by simpa [childHi] using upper'
    upperCylinder := by simpa [childHi] using hupperCylinder
    upperLiteral := by
      intro q hqL hqU
      simpa [childHi] using hupperLiteral q hqL hqU
    upperCovers := hupperCovers
    endpointSeparation := by simpa [childHi] using hendpointSeparation
  }

#print axioms profiledGapStageOfTwoSheet
#print axioms ProfiledGapStage.hasNextCoeffProfile_of_ready
#print axioms ProfiledGapStage.advanceOfNextCoeffProfile

end Erdos249257.SuffixCylinderProfiledGap
