import Erdos249257.SuffixCylinderInStrip

/-!
# Structure-preserving continuation of a finite suffix-cylinder gap

The in-strip feedback split retains two live cylinder sheets but its first
successor theorem previously returned only pointwise reachability.  This file
packages the complement of an arbitrary closed carry gap and propagates that
package through one genuinely common-coefficient row.  The parent gap
`[a,b]` becomes the exact child gap `[2a-C-1, 2b-C]`; both selected families,
their suffix-cylinder endpoints, and their complementary literal prefixes
survive the step.
-/

namespace Erdos249257.SuffixCylinderFiniteGap

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderPromotion
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderInStrip

/-- Canonical fixed-coefficient successor of a selected carry interval.
Unlike `SelectedHalfInterval.stepTailExplicit`, both endpoints of the parent
interval are explicit inputs, so this constructor can be iterated on an
already shifted upper sheet. -/
noncomputable def selectedHalfIntervalStepExplicit
    {N L U L' U' C : ℕ} (hN : 1 ≤ N)
    (W : SelectedHalfInterval N L U)
    (hL'pos : 1 ≤ L') (hU'strip : U' ≤ halfStripBound (N + 1))
    (hparentLo : ∀ q : ℕ, L' ≤ q → q ≤ U' → L ≤ parent C q)
    (hparentHi : ∀ q : ℕ, L' ≤ q → q ≤ U' → parent C q ≤ U)
    (hcoeff : ∀ k : ℕ, ∀ hkL : L ≤ k, ∀ hkU : k ≤ U,
      supportCoeff (wordSupport (W.word k hkL hkU)) (N + 1) = C) :
    SelectedHalfInterval (N + 1) L' U' := by
  classical
  let bit (q : ℕ) : Bool := decide (explicitParentBitZ C q = 1)
  let child (q : ℕ) (hqL : L' ≤ q) (hqU : q ≤ U') : HalfWord (N + 1) :=
    extendHalfWord
      (W.word (parent C q) (hparentLo q hqL hqU) (hparentHi q hqL hqU))
      (bit q)
  have childTerminal (q : ℕ) (hqL : L' ≤ q) (hqU : q ≤ U') :
      integerHalfCarry (wordSupport (child q hqL hqU)) N = q := by
    let k := parent C q
    have hkL : L ≤ k := hparentLo q hqL hqU
    have hkU : k ≤ U := hparentHi q hqL hqU
    let a := W.word k hkL hkU
    have hkcarry := W.terminal k hkL hkU
    have hparentCarry :
        integerHalfCarry (wordSupport (child q hqL hqU)) (N - 1) = k := by
      have hfuture := integerHalfCarry_insert_future_eq (wordSupport a)
        (show N - 1 + 2 ≤ N + 1 by omega)
      dsimp [child, a, k]
      rw [wordSupport_extendHalfWord]
      cases hbit : bit q
      · simpa [hbit] using hkcarry
      · simpa [hbit] using hfuture.trans hkcarry
    have hbaseCoeff : supportCoeff (wordSupport a) (N + 1) = C := by
      simpa [a] using hcoeff k hkL hkU
    have hchildCoeff :
        (supportCoeff (wordSupport (child q hqL hqU)) (N + 1) : ℤ) =
          C + explicitParentBitZ C q := by
      rcases explicitParentBitZ_zero_or_one C q with hb | hb
      · have hbit : bit q = false := by simp [bit, hb]
        have hsupp : wordSupport (child q hqL hqU) = wordSupport a := by
          change wordSupport (extendHalfWord a (bit q)) = wordSupport a
          rw [wordSupport_extendHalfWord]
          simp [hbit]
        rw [hsupp]
        have hbaseCoeffZ : (supportCoeff (wordSupport a) (N + 1) : ℤ) = C := by
          exact_mod_cast hbaseCoeff
        simpa [hb] using hbaseCoeffZ
      · have hbit : bit q = true := by simp [bit, hb]
        have hsupp : wordSupport (child q hqL hqU) =
            insert (N + 1) (wordSupport a) := by
          change wordSupport (extendHalfWord a (bit q)) =
            insert (N + 1) (wordSupport a)
          rw [wordSupport_extendHalfWord]
          simp [hbit]
        rw [hsupp]
        rw [Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_self
          _ (by omega)]
        · push_cast
          rw [hbaseCoeff]
          simp [hb]
        · intro hmem
          rcases hmem with ⟨hlt, -⟩
          omega
    have hrec := integerHalfCarry_succ
      (wordSupport (child q hqL hqU)) (N - 1)
    simp only [show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega] at hrec
    calc
      integerHalfCarry (wordSupport (child q hqL hqU)) N =
          2 * integerHalfCarry (wordSupport (child q hqL hqU)) (N - 1) -
            (supportCoeff (wordSupport (child q hqL hqU)) (N + 1) : ℤ) := hrec
      _ = 2 * (k : ℤ) - (C + explicitParentBitZ C q) := by
        rw [hparentCarry, hchildCoeff]
      _ = q := by
        dsimp [k]
        rw [explicitParent_recurrence C q]
        ring
  exact {
    word := child
    admissible := by
      intro q hqL hqU
      let k := parent C q
      have hkL : L ≤ k := hparentLo q hqL hqU
      have hkU : k ≤ U := hparentHi q hqL hqU
      apply HalfStripAdmissible.extend hN (W.admissible k hkL hkU)
      rw [childTerminal q hqL hqU]
      exact ⟨by exact_mod_cast hL'pos.trans hqL,
        by exact_mod_cast hqU.trans hU'strip⟩
    terminal := by
      intro q hqL hqU
      simpa [show N + 1 - 1 = N by omega] using childTerminal q hqL hqU
  }

theorem selectedHalfIntervalWord_stepExplicit
    {N L U L' U' C : ℕ} (hN : 1 ≤ N)
    (W : SelectedHalfInterval N L U)
    (hL'pos : 1 ≤ L') (hU'strip : U' ≤ halfStripBound (N + 1))
    (hparentLo : ∀ q : ℕ, L' ≤ q → q ≤ U' → L ≤ parent C q)
    (hparentHi : ∀ q : ℕ, L' ≤ q → q ≤ U' → parent C q ≤ U)
    (hcoeff : ∀ k : ℕ, ∀ hkL : L ≤ k, ∀ hkU : k ≤ U,
      supportCoeff (wordSupport (W.word k hkL hkU)) (N + 1) = C)
    (q : ℕ) (hqL : L' ≤ q) (hqU : q ≤ U') :
    (selectedHalfIntervalStepExplicit hN W hL'pos hU'strip
      hparentLo hparentHi hcoeff).word
        q hqL hqU =
      extendHalfWord
        (W.word (parent C q) (hparentLo q hqL hqU)
          (hparentHi q hqL hqU))
        (decide (explicitParentBitZ C q = 1)) := by
  rfl

/-- A shifted interval successor preserves a common literal prefix. -/
theorem selectedHalfIntervalStepExplicit_preserves_literalPrefix
    {M N L U L' U' C : ℕ} (W : SelectedHalfInterval N L U)
    (hMN : M ≤ N) (pfx : HalfWord M)
    (hN : 1 ≤ N) (hL'pos : 1 ≤ L')
    (hU'strip : U' ≤ halfStripBound (N + 1))
    (hparentLo : ∀ q : ℕ, L' ≤ q → q ≤ U' → L ≤ parent C q)
    (hparentHi : ∀ q : ℕ, L' ≤ q → q ≤ U' → parent C q ≤ U)
    (hcoeff : ∀ k : ℕ, ∀ hkL : L ≤ k, ∀ hkU : k ≤ U,
      supportCoeff (wordSupport (W.word k hkL hkU)) (N + 1) = C)
    (hpfx : ∀ k (hkL : L ≤ k) (hkU : k ≤ U),
      restrictWord hMN (W.word k hkL hkU) = pfx) :
    ∀ q (hqL : L' ≤ q) (hqU : q ≤ U'),
      restrictWord (hMN.trans (Nat.le_succ N))
        ((selectedHalfIntervalStepExplicit hN W hL'pos hU'strip
          hparentLo hparentHi hcoeff).word
          q hqL hqU) = pfx := by
  intro q hqL hqU
  rw [selectedHalfIntervalWord_stepExplicit]
  rw [← restrictWord_trans hMN (Nat.le_succ N)]
  rw [restrictWord_extendHalfWord]
  exact hpfx (parent C q) (hparentLo q hqL hqU) (hparentHi q hqL hqU)

/-- Endpoint-cylinder propagation for a shifted selected interval. -/
theorem selectedHalfIntervalHasSuffixCylinderOnInterval_stepExplicit
    {M N L U L' U' C E : ℕ} (W : SelectedHalfInterval N L U)
    (hMN : M ≤ N) (hN : 1 ≤ N) (hL'pos : 1 ≤ L')
    (hU'strip : U' ≤ halfStripBound (N + 1))
    (hparentLo : ∀ q : ℕ, L' ≤ q → q ≤ U' → L ≤ parent C q)
    (hparentHi : ∀ q : ℕ, L' ≤ q → q ≤ U' → parent C q ≤ U)
    (hcoeff : ∀ k : ℕ, ∀ hkL : L ≤ k, ∀ hkU : k ≤ U,
      supportCoeff (wordSupport (W.word k hkL hkU)) (N + 1) = C)
    (hcyl : HasSuffixCylinderOnInterval W hMN E)
    (hCE : C ≤ 2 * E) :
    HasSuffixCylinderOnInterval
      (selectedHalfIntervalStepExplicit hN W hL'pos hU'strip
        hparentLo hparentHi hcoeff)
      (hMN.trans (Nat.le_succ N)) (2 * E - C) := by
  classical
  rcases hcyl with ⟨pfx, hcyl⟩
  refine ⟨pfx, ?_⟩
  intro q hqL hqU
  let k := parent C q
  have hkL : L ≤ k := hparentLo q hqL hqU
  have hkU : k ≤ U := hparentHi q hqL hqU
  obtain ⟨hprefix, hendpoint⟩ := hcyl k hkL hkU
  constructor
  · rw [selectedHalfIntervalWord_stepExplicit]
    rw [← restrictWord_trans hMN (Nat.le_succ N)]
    rw [restrictWord_extendHalfWord]
    exact hprefix
  · rw [selectedHalfIntervalWord_stepExplicit]
    rw [supportSuffixNumeral_extendHalfWord hMN]
    have hbit := explicitParent_bitNat_recurrence C q
    dsimp [k] at hendpoint
    omega

/-- A reusable two-sheet state whose missing terminal carries form one
closed interval. -/
structure InStripGapStage (K N : ℕ) where
  hK1N : K + 1 ≤ N
  gapLo : ℕ
  gapHi : ℕ
  gapLo_pos : 1 ≤ gapLo
  gap_order : gapLo ≤ gapHi
  gapHi_le : gapHi ≤ halfStripBound N
  boundaryPrefix : HalfWord K
  lower : SelectedHalfWindow N (gapLo - 1)
  lowerCylinder : HasSuffixCylinderAt lower hK1N (gapLo - 1)
  lowerLiteral : ∀ q (hq : 1 ≤ q) (hqR : q ≤ gapLo - 1),
    restrictWord hK1N (lower.word q hq hqR) =
      extendHalfWord boundaryPrefix true
  upperEndpoint : ℕ
  upper : SelectedHalfInterval N (gapHi + 1) (halfStripBound N)
  upperCylinder : HasSuffixCylinderOnInterval upper hK1N upperEndpoint
  upperLiteral : ∀ q (hqL : gapHi + 1 ≤ q)
      (hqU : q ≤ halfStripBound N),
    restrictWord hK1N (upper.word q hqL hqU) =
      extendHalfWord boundaryPrefix false
  upperCovers : halfStripBound N ≤ upperEndpoint

def InStripGapStage.HasCommonNextCoeff
    {K N : ℕ} (T : InStripGapStage K N) (C : ℕ) : Prop :=
  (∀ q (hq : 1 ≤ q) (hqR : q ≤ T.gapLo - 1),
    supportCoeff (wordSupport (T.lower.word q hq hqR)) (N + 1) = C) ∧
  (∀ q (hqL : T.gapHi + 1 ≤ q) (hqU : q ≤ halfStripBound N),
    supportCoeff (wordSupport (T.upper.word q hqL hqU)) (N + 1) = C)

/-- The one-hole feedback state is the singleton-gap instance. -/
noncomputable def inStripGapStageOfTwoSheet
    {K N : ℕ} (T : InStripTwoSheetStage K N) :
    InStripGapStage K N where
  hK1N := T.hK1N
  gapLo := T.hole
  gapHi := T.hole
  gapLo_pos := T.hole_pos
  gap_order := le_rfl
  gapHi_le := T.hole_le
  boundaryPrefix := T.boundaryPrefix
  lower := T.lower
  lowerCylinder := T.lowerCylinder
  lowerLiteral := T.lowerLiteral
  upperEndpoint := T.upperEndpoint
  upper := T.upper
  upperCylinder := T.upperCylinder
  upperLiteral := T.upperLiteral
  upperCovers := T.upperCovers

theorem inStripGapStageOfTwoSheet_hasCommonNextCoeff
    {K N C : ℕ} (T : InStripTwoSheetStage K N)
    (hcommon : T.HasCommonNextCoeff C) :
    (inStripGapStageOfTwoSheet T).HasCommonNextCoeff C := hcommon

/-- **Structure-preserving finite-gap successor.**  If both live sheets have
one common next coefficient and the doubled child gap remains inside the next
strip, propagate the complete two-sheet package by one row. -/
noncomputable def InStripGapStage.advanceOfCommonNextCoeff
    {K N C : ℕ} (T : InStripGapStage K N)
    (hN : 1 ≤ N)
    (hcommon : T.HasCommonNextCoeff C)
    (hchildLoPos : 1 ≤ 2 * T.gapLo - C - 1)
    (hchildHiStrip : 2 * T.gapHi - C ≤ halfStripBound (N + 1))
    (hbuffer : halfStripBound (N + 1) + C ≤ 2 * halfStripBound N) :
    InStripGapStage K (N + 1) := by
  let childLo := 2 * T.gapLo - C - 1
  let childHi := 2 * T.gapHi - C
  have hgapOrder : T.gapLo ≤ T.gapHi := T.gap_order
  have hClo : C + 1 ≤ 2 * T.gapLo := by omega
  have hChi : C ≤ 2 * T.gapHi := by omega
  have hchildOrder : childLo ≤ childHi := by
    dsimp [childLo, childHi]
    omega
  have hchildHiStrip' : childHi ≤ halfStripBound (N + 1) := by
    simpa [childHi] using hchildHiStrip
  let lowerRange := childLo - 1
  have hlowerRangeEq : lowerRange = 2 * (T.gapLo - 1) - C := by
    dsimp [lowerRange, childLo]
    omega
  have hlowerStrip : lowerRange ≤ halfStripBound (N + 1) := by
    dsimp [lowerRange]
    exact (Nat.pred_le childLo).trans hchildOrder |>.trans hchildHiStrip'
  have hlowerCoeff : ∀ k : ℕ, 1 ≤ k → k ≤ T.gapLo - 1 →
      selectedRowCoeff T.lower k = C := by
    intro k hk hkR
    rw [selectedRowCoeff, dif_pos ⟨hk, hkR⟩]
    exact_mod_cast hcommon.1 k hk hkR
  have hlowerBuffer : lowerRange + C ≤ 2 * (T.gapLo - 1) := by
    rw [hlowerRangeEq]
    omega
  let lower' : SelectedHalfWindow (N + 1) lowerRange :=
    T.lower.stepExplicit hN hlowerStrip hlowerCoeff hlowerBuffer
  have hlowerCylinder :=
    SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
      hN T.lower T.hK1N hlowerStrip hlowerCoeff hlowerBuffer
      T.lowerCylinder (le_refl (T.gapLo - 1))
  have hlowerLiteral : ∀ q (hq : 1 ≤ q) (hqR : q ≤ lowerRange),
      restrictWord (T.hK1N.trans (Nat.le_succ N))
        (lower'.word q hq hqR) = extendHalfWord T.boundaryPrefix true := by
    intro q hq hqR
    exact SelectedHalfWindow.stepExplicit_preserves_literalPrefix
      T.lower T.hK1N (extendHalfWord T.boundaryPrefix true)
      hN hlowerStrip hlowerCoeff hlowerBuffer T.lowerLiteral q hq hqR
  have hparentLo : ∀ q : ℕ, childHi + 1 ≤ q →
      q ≤ halfStripBound (N + 1) → T.gapHi + 1 ≤ parent C q := by
    intro q hqL hqU
    have hrec := explicitParent_bitNat_recurrence C q
    dsimp [childHi] at hqL
    omega
  have hparentHi : ∀ q : ℕ, childHi + 1 ≤ q →
      q ≤ halfStripBound (N + 1) → parent C q ≤ halfStripBound N := by
    intro q hqL hqU
    exact explicitParent_le hqU hbuffer
  let upper' : SelectedHalfInterval (N + 1) (childHi + 1)
      (halfStripBound (N + 1)) :=
    selectedHalfIntervalStepExplicit hN T.upper (by omega) le_rfl
      hparentLo hparentHi hcommon.2
  have hCE : C ≤ 2 * T.upperEndpoint := by
    have hCB : C ≤ 2 * halfStripBound N := by omega
    exact hCB.trans (Nat.mul_le_mul_left 2 T.upperCovers)
  have hupperCylinder : HasSuffixCylinderOnInterval upper'
      (T.hK1N.trans (Nat.le_succ N)) (2 * T.upperEndpoint - C) := by
    exact selectedHalfIntervalHasSuffixCylinderOnInterval_stepExplicit
      T.upper T.hK1N hN (by omega) le_rfl hparentLo hparentHi hcommon.2
      T.upperCylinder hCE
  have hupperLiteral : ∀ q (hqL : childHi + 1 ≤ q)
      (hqU : q ≤ halfStripBound (N + 1)),
      restrictWord (T.hK1N.trans (Nat.le_succ N))
        (upper'.word q hqL hqU) = extendHalfWord T.boundaryPrefix false := by
    intro q hqL hqU
    exact selectedHalfIntervalStepExplicit_preserves_literalPrefix
      T.upper T.hK1N (extendHalfWord T.boundaryPrefix false)
      hN (by omega) le_rfl hparentLo hparentHi hcommon.2 T.upperLiteral
      q hqL hqU
  have hupperCovers : halfStripBound (N + 1) ≤
      2 * T.upperEndpoint - C := by
    have hbase : halfStripBound (N + 1) + C ≤ 2 * T.upperEndpoint :=
      hbuffer.trans (Nat.mul_le_mul_left 2 T.upperCovers)
    omega
  exact {
    hK1N := T.hK1N.trans (Nat.le_succ N)
    gapLo := childLo
    gapHi := childHi
    gapLo_pos := by simpa [childLo] using hchildLoPos
    gap_order := hchildOrder
    gapHi_le := hchildHiStrip'
    boundaryPrefix := T.boundaryPrefix
    lower := by simpa [lowerRange, childLo] using lower'
    lowerCylinder := by
      simpa [lowerRange, childLo, hlowerRangeEq] using hlowerCylinder.1
    lowerLiteral := by
      intro q hq hqR
      simpa [lowerRange, childLo] using hlowerLiteral q hq hqR
    upperEndpoint := 2 * T.upperEndpoint - C
    upper := by simpa [childHi] using upper'
    upperCylinder := by simpa [childHi] using hupperCylinder
    upperLiteral := by
      intro q hqL hqU
      simpa [childHi] using hupperLiteral q hqL hqU
    upperCovers := hupperCovers
  }

#print axioms selectedHalfIntervalStepExplicit
#print axioms selectedHalfIntervalHasSuffixCylinderOnInterval_stepExplicit
#print axioms inStripGapStageOfTwoSheet
#print axioms InStripGapStage.advanceOfCommonNextCoeff

end Erdos249257.SuffixCylinderFiniteGap
