import Erdos249257.SuffixCylinderGlobalProducer

/-!
# Upper-sheet recylindrification when the crossing hole is below the strip
-/

namespace Erdos249257.SuffixCylinderBelow

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderPromotion
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderGlobalProducer

/-- Explicit fixed-coefficient successor which only requires the coefficient
hypothesis on the canonical parents actually used.  This is the minimal
upper-sheet reindexing abstraction: the parent interval need not start at
carry one. -/
noncomputable def SelectedHalfWindow.stepTailExplicit
    {N R S C δ : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hbuffer : S + C ≤ 2 * R)
    (hparentTail : ∀ q : ℕ, 1 ≤ q → q ≤ S → δ < parent C q)
    (hcoeff : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R), δ < k →
      supportCoeff (wordSupport (W.word k hk hkR)) (N + 1) = C) :
    SelectedHalfWindow (N + 1) S := by
  classical
  let bit (q : ℕ) : Bool := decide (explicitParentBitZ C q = 1)
  let child (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) : HalfWord (N + 1) :=
    extendHalfWord
      (W.word (parent C q) (explicitParent_pos hq)
        (explicitParent_le hqS hbuffer))
      (bit q)
  have childTerminal (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) :
      integerHalfCarry (wordSupport (child q hq hqS)) N = q := by
    let k := parent C q
    have hk : 1 ≤ k := explicitParent_pos hq
    have hkR : k ≤ R := explicitParent_le hqS hbuffer
    have hkTail : δ < k := hparentTail q hq hqS
    let a := W.word k hk hkR
    have hkcarry := W.terminal k hk hkR
    have hparentCarry :
        integerHalfCarry (wordSupport (child q hq hqS)) (N - 1) = k := by
      have hfuture := integerHalfCarry_insert_future_eq (wordSupport a)
        (show N - 1 + 2 ≤ N + 1 by omega)
      dsimp [child, a, k]
      rw [wordSupport_extendHalfWord]
      cases hbit : bit q
      · simpa [hbit] using hkcarry
      · simpa [hbit] using hfuture.trans hkcarry
    have hbaseCoeff : supportCoeff (wordSupport a) (N + 1) = C := by
      simpa [a] using hcoeff k hk hkR hkTail
    have hchildCoeff :
        (supportCoeff (wordSupport (child q hq hqS)) (N + 1) : ℤ) =
          C + explicitParentBitZ C q := by
      rcases explicitParentBitZ_zero_or_one C q with hb | hb
      · have hbit : bit q = false := by simp [bit, hb]
        have hsupp : wordSupport (child q hq hqS) = wordSupport a := by
          change wordSupport (extendHalfWord a (bit q)) = wordSupport a
          rw [wordSupport_extendHalfWord]
          simp [hbit]
        rw [hsupp]
        have hbaseCoeffZ :
            (supportCoeff (wordSupport a) (N + 1) : ℤ) = C := by
          exact_mod_cast hbaseCoeff
        simpa [hb] using hbaseCoeffZ
      · have hbit : bit q = true := by simp [bit, hb]
        have hsupp : wordSupport (child q hq hqS) =
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
      (wordSupport (child q hq hqS)) (N - 1)
    simp only [show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega] at hrec
    calc
      integerHalfCarry (wordSupport (child q hq hqS)) N =
          2 * integerHalfCarry (wordSupport (child q hq hqS)) (N - 1) -
            (supportCoeff (wordSupport (child q hq hqS)) (N + 1) : ℤ) := hrec
      _ = 2 * (k : ℤ) - (C + explicitParentBitZ C q) := by
        rw [hparentCarry, hchildCoeff]
      _ = q := by
        dsimp [k]
        rw [explicitParent_recurrence C q]
        ring
  exact {
    word := child
    admissible := by
      intro q hq hqS
      let k := parent C q
      have hk : 1 ≤ k := explicitParent_pos hq
      have hkR : k ≤ R := explicitParent_le hqS hbuffer
      apply HalfStripAdmissible.extend hN (W.admissible k hk hkR)
      rw [childTerminal q hq hqS]
      exact ⟨by exact_mod_cast hq, by exact_mod_cast hqS.trans hSstrip⟩
    terminal := by
      intro q hq hqS
      simpa [show N + 1 - 1 = N by omega] using childTerminal q hq hqS
  }

/-- The upper-sheet successor is definitionally the canonical fixed-`C`
parent with its parity bit appended. -/
theorem SelectedHalfWindow.word_stepTailExplicit
    {N R S C δ : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hbuffer : S + C ≤ 2 * R)
    (hparentTail : ∀ q : ℕ, 1 ≤ q → q ≤ S → δ < parent C q)
    (hcoeff : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R), δ < k →
      supportCoeff (wordSupport (W.word k hk hkR)) (N + 1) = C)
    (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) :
    (Erdos249257.SuffixCylinderBelow.SelectedHalfWindow.stepTailExplicit
      hN W hSstrip hbuffer hparentTail hcoeff).word q hq hqS =
      extendHalfWord
        (W.word (parent C q) (explicitParent_pos hq)
          (explicitParent_le hqS hbuffer))
        (decide (explicitParentBitZ C q = 1)) := by
  rfl

/-- If the crossing hole lies below carry one, every target in the next full
strip uses the false-bit upper parent sheet.  Reindexing that tail by the
canonical fixed-`c` parent yields a new full endpoint cylinder. -/
noncomputable def CylinderStage.feedbackAdvanceCrossingBelow
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hcrossLow : 2 ^ (N - (K + 1)) < S.endpoint)
    (hcrossHigh :
      S.endpoint < 2 ^ (N - (K + 1)) + halfStripBound N)
    (c : ℕ)
    (hprofile : ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound N),
      supportCoeff (wordSupport (S.window.word k hk hkR)) (N + 1) =
        if k ≤ S.endpoint - 2 ^ (N - (K + 1)) then c + 1 else c)
    (hholeBelow :
      2 * (S.endpoint - 2 ^ (N - (K + 1))) - c < 1) :
    CylinderStage (K + 1) (N + 1) := by
  classical
  let δ := S.endpoint - 2 ^ (N - (K + 1))
  have hδpos : 1 ≤ δ := by
    dsimp [δ]
    omega
  have hδltR : δ < halfStripBound N := by
    dsimp [δ]
    omega
  have hR : 1 ≤ halfStripBound N := hδpos.trans hδltR.le
  have hcoeffR := hprofile (halfStripBound N) hR le_rfl
  rw [if_neg (by omega : ¬ halfStripBound N ≤ δ)] at hcoeffR
  let aR := S.window.word (halfStripBound N) hR le_rfl
  have hc : c ≤ 2 * Nat.sqrt (N + 1) := by
    rw [← hcoeffR]
    exact supportCoeff_le_two_mul_sqrt (wordSupport aR) (N + 1)
  have hbuffer : halfStripBound (N + 1) + c ≤ 2 * halfStripBound N := by
    simpa using halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := c) (by omega) hc
  have hparentTail : ∀ q : ℕ, 1 ≤ q → q ≤ halfStripBound (N + 1) →
      δ < parent c q := by
    intro q hq hqS
    have hrec := explicitParent_bitNat_recurrence c q
    by_contra hnot
    have hle : parent c q ≤ δ := by omega
    omega
  have hcoeffTail : ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound N),
      δ < k →
      supportCoeff (wordSupport (S.window.word k hk hkR)) (N + 1) = c := by
    intro k hk hkR hkTail
    have hp := hprofile k hk hkR
    rw [if_neg (by omega : ¬ k ≤ δ)] at hp
    exact hp
  let W' : SelectedHalfWindow (N + 1) (halfStripBound (N + 1)) :=
    Erdos249257.SuffixCylinderBelow.SelectedHalfWindow.stepTailExplicit
      hN S.window le_rfl hbuffer hparentTail hcoeffTail
  let pfx : HalfWord K := Classical.choose S.cylinder
  have hcyl := Classical.choose_spec S.cylinder
  have hcyl' : HasSuffixCylinderAt W'
      (hK1N.trans (Nat.le_succ N)) (2 * S.endpoint - c) := by
    refine ⟨extendHalfWord pfx false, ?_⟩
    intro q hq hqS
    let k := parent c q
    have hk : 1 ≤ k := explicitParent_pos hq
    have hkR : k ≤ halfStripBound N := explicitParent_le hqS hbuffer
    have hkTail : δ < k := hparentTail q hq hqS
    have hparentPrefix := (hcyl k hk hkR).1
    have hparentEndpoint := (hcyl k hk hkR).2
    have hbitFalse : S.window.word k hk hkR ⟨K + 1, by omega⟩ = false := by
      cases hb : S.window.word k hk hkR ⟨K + 1, by omega⟩ with
      | false => rfl
      | true =>
          have hkle :=
            (headBit_true_iff_le_crossingCut S.window hK1N
              ⟨pfx, hcyl⟩ hcrossLow hk hkR).1 hb
          exact False.elim ((by omega : ¬ k ≤ δ) hkle)
    have hparentPromoted :
        restrictWord hK1N (S.window.word k hk hkR) =
          extendHalfWord pfx false :=
      restrictWord_succ_eq_extendHalfWord hK1N
        (S.window.word k hk hkR) pfx false hparentPrefix hbitFalse
    constructor
    · rw [Erdos249257.SuffixCylinderBelow.SelectedHalfWindow.word_stepTailExplicit]
      rw [← restrictWord_trans hK1N (Nat.le_succ N)]
      rw [restrictWord_extendHalfWord]
      exact hparentPromoted
    · rw [Erdos249257.SuffixCylinderBelow.SelectedHalfWindow.word_stepTailExplicit]
      rw [supportSuffixNumeral_extendHalfWord hK1N]
      change
        2 * wordSuffixNumeral (S.window.word k hk hkR)
              (K + 1) (N - (K + 1)) +
            (if decide (explicitParentBitZ c q = 1) then 1 else 0) + q =
          2 * S.endpoint - c
      have hsplit := wordSuffixNumeral_split_head hK1N
        (S.window.word k hk hkR)
      rw [hbitFalse] at hsplit
      have hbitRec := explicitParent_bitNat_recurrence c q
      change wordSuffixNumeral (S.window.word k hk hkR) K (N - K) + k =
        S.endpoint at hparentEndpoint
      change wordSuffixNumeral (S.window.word k hk hkR) K (N - K) =
        0 + wordSuffixNumeral (S.window.word k hk hkR)
          (K + 1) (N - (K + 1)) at hsplit
      omega
  have hcover : halfStripBound (N + 1) ≤ 2 * S.endpoint - c := by
    have hbase := S.covers
    omega
  exact ⟨hK1N.trans (Nat.le_succ N), W', 2 * S.endpoint - c,
    hcyl', hcover⟩

#print axioms SelectedHalfWindow.stepTailExplicit
#print axioms SelectedHalfWindow.word_stepTailExplicit
#print axioms CylinderStage.feedbackAdvanceCrossingBelow

end Erdos249257.SuffixCylinderBelow
