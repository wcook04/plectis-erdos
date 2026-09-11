import Erdos249257.HalfCarryRewindPhase
import Erdos249257.HalfCarrySelectedWindowBase

/-!
# Terminally indexed selected cylinders

The executable tree is not merely a family of terminal representatives: its
suffix numeral plus its terminal carry is one common endpoint.  This module
records that invariant and its exact propagation under the canonical selected
window successor.
-/

namespace Erdos249257.SelectedSuffixCylinder

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.HalfCarrySelectedWindowBase
open Erdos249257.FixedCoeffRewind
open Erdos249257.FixedCoeffRewindPhase

/-- Binary value of the indicated terminal word suffix. -/
noncomputable def wordSuffixNumeral
    {N : ℕ} (a : HalfWord N) (M L : ℕ) : ℕ :=
  @supportSuffixNumeral (wordSupport a) (Classical.decPred _) M L

/-- A selected window shares one prefix, while its suffix numerals are the
consecutive values `endpoint - k` indexed by terminal carry `k`. -/
noncomputable def HasSuffixCylinderAt
    {M N R : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N)
    (endpoint : ℕ) : Prop :=
  ∃ pfx : HalfWord M,
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord hMN (W.word k hk hkR) = pfx ∧
        wordSuffixNumeral (W.word k hk hkR) M (N - M) + k =
          endpoint

/-- A support suffix numeral depends only on membership in the suffix
interval that it reads. -/
theorem supportSuffixNumeral_congr_on
    (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (M L : ℕ)
    (hbits : ∀ j : ℕ, j < L → (M + j + 1 ∈ A ↔ M + j + 1 ∈ B)) :
    supportSuffixNumeral A M L = supportSuffixNumeral B M L := by
  induction L with
  | zero => simp [supportSuffixNumeral]
  | succ L ih =>
      rw [supportSuffixNumeral, supportSuffixNumeral,
        ih (fun j hj ↦ hbits j (by omega))]
      have hlast := hbits L (by omega)
      by_cases hA : M + L + 1 ∈ A <;>
        by_cases hB : M + L + 1 ∈ B <;> simp [hA, hB] at hlast ⊢

/-- Appending one bit doubles the old suffix numeral and adds that bit. -/
theorem supportSuffixNumeral_extendHalfWord
    {M N : ℕ} (hMN : M ≤ N) (a : HalfWord N) (β : Bool) :
    wordSuffixNumeral (extendHalfWord a β) M (N + 1 - M) =
      2 * wordSuffixNumeral a M (N - M) +
        if β then 1 else 0 := by
  classical
  unfold wordSuffixNumeral
  rw [show N + 1 - M = (N - M) + 1 by omega, supportSuffixNumeral]
  rw [show M + (N - M) + 1 = N + 1 by omega]
  rw [supportSuffixNumeral_congr_on
    (wordSupport (extendHalfWord a β)) (wordSupport a) M (N - M)]
  · have hnmem : N + 1 ∉ wordSupport a := by
      rintro ⟨hN, -⟩
      omega
    cases β <;> simp [mem_wordSupport_extendHalfWord_iff, hnmem]
  · intro j hj
    rw [mem_wordSupport_extendHalfWord_iff]
    constructor
    · rintro (h | ⟨hindex, -⟩)
      · exact h
      · omega
    · exact Or.inl

/-- The finite depth-18 cylinder has common endpoint 17 after its common
depth-13 prefix is removed. -/
theorem depth18Word_suffix_thirteen
    {k : ℕ} (hk : 1 ≤ k) (hk12 : k ≤ 12) :
    wordSuffixNumeral (depth18Word k) 13 5 + k = 17 := by
  interval_cases k <;>
    norm_num [wordSuffixNumeral, supportSuffixNumeral, wordSupport,
      depth18Word]

/-- Exact cylinder certificate for the existing certified induction base. -/
theorem depth18SelectedHalfWindow_hasSuffixCylinderAt_thirteen :
    HasSuffixCylinderAt depth18SelectedHalfWindow (by omega : 13 ≤ 18) 17 := by
  refine ⟨depth18PrefixWord, ?_⟩
  intro k hk hkR
  constructor
  · change restrictWord (by omega : 13 ≤ 18) (depth18Word k) =
      depth18PrefixWord
    exact restrictWord_depth18Word_thirteen k
  · change wordSuffixNumeral (depth18Word k) 13 5 + k = 17
    apply depth18Word_suffix_thirteen hk
    simpa [halfStripBound_eighteen] using hkR

/-- The depth-18 endpoint covers its complete certified strip. -/
theorem depth18SelectedHalfWindow_endpoint_covers_strip :
    halfStripBound 18 ≤ 17 := by
  norm_num [halfStripBound_eighteen]

/-- The public selected successor really is the canonical parent word with
the explicit parity bit appended. -/
theorem SelectedHalfWindow.word_stepExplicit
    {N R S C : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R → selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R)
    (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) :
    (W.stepExplicit hN hSstrip hp_common hbuffer).word q hq hqS =
      extendHalfWord
        (W.word (parent C q) (explicitParent_pos hq)
          (explicitParent_le hqS hbuffer))
        (decide (explicitParentBitZ C q = 1)) := by
  rfl

/-- Natural-number form of the canonical parent/bit recurrence. -/
theorem explicitParent_bitNat_recurrence (C q : ℕ) :
    q + C + (if decide (explicitParentBitZ C q = 1) then 1 else 0) =
      2 * parent C q := by
  rcases explicitParentBitZ_zero_or_one C q with hzero | hone
  · have hz : ¬ explicitParentBitZ C q = 1 := by omega
    rw [if_neg (by simpa using hz)]
    simp only [explicitParentBitZ] at hzero
    omega
  · rw [if_pos (by simpa using hone)]
    simp only [explicitParentBitZ] at hone
    omega

/-- Exact cylinder propagation. The endpoint update is `E' = 2E-C`; the
ordinary selected-window buffer also proves that the new endpoint still
covers the entire new carry interval. -/
theorem SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
    {M N R S C E : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hMN : M ≤ N)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R → selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R)
    (hcyl : HasSuffixCylinderAt W hMN E)
    (hRE : R ≤ E) :
    HasSuffixCylinderAt (W.stepExplicit hN hSstrip hp_common hbuffer)
        (hMN.trans (Nat.le_succ N)) (2 * E - C) ∧
      S ≤ 2 * E - C := by
  classical
  have hCE : C ≤ 2 * E := by omega
  rcases hcyl with ⟨pfx, hcyl⟩
  constructor
  · refine ⟨pfx, ?_⟩
    intro q hq hqS
    let k := parent C q
    have hk : 1 ≤ k := explicitParent_pos hq
    have hkR : k ≤ R := explicitParent_le hqS hbuffer
    obtain ⟨hprefix, hendpoint⟩ := hcyl k hk hkR
    constructor
    · rw [← restrictWord_trans hMN (Nat.le_succ N)]
      rw [W.restrictWord_stepExplicit hN hSstrip hp_common hbuffer q hq hqS]
      exact hprefix
    · rw [SelectedSuffixCylinder.SelectedHalfWindow.word_stepExplicit
          hN W hSstrip hp_common hbuffer q hq hqS]
      rw [supportSuffixNumeral_extendHalfWord hMN]
      have hbit := explicitParent_bitNat_recurrence C q
      dsimp [k] at hendpoint
      omega
  · omega

#print axioms supportSuffixNumeral_extendHalfWord
#print axioms depth18Word_suffix_thirteen
#print axioms depth18SelectedHalfWindow_hasSuffixCylinderAt_thirteen
#print axioms depth18SelectedHalfWindow_endpoint_covers_strip
#print axioms SelectedHalfWindow.word_stepExplicit
#print axioms explicitParent_bitNat_recurrence
#print axioms SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit

end Erdos249257.SelectedSuffixCylinder
