import Mathlib

namespace Erdos249257.ExternalVerification257ActualUpperSuccessor

open Set
open scoped BigOperators

noncomputable section

def seamIntegerGreedyRemainder (_s : ℕ) : ℕ := 0

structure SeamAdjacentCutView where
  successorCarries : Prop
  belowPulse : ℕ

def seamAdjacentCut (_s : ℕ) (_hs : 5 ≤ _s) : SeamAdjacentCutView where
  successorCarries := False
  belowPulse := 0

def affineRightRunCharge (pulse : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 4 * affineRightRunCharge pulse k + pulse k + 4

def SeamActualUpperRightPacketLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) + 2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    4 ^ k * (2 * (d + k)) ≤ seamIntegerGreedyRemainder (d + k + 1) +
      affineRightRunCharge
        (fun q ↦ (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k

def SeamActualUpperSuccessorLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) + 2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    2 ^ (d + 1) - 2 ^ (d - k + 1) + 2 * (d + k) ≤
      seamIntegerGreedyRemainder (d + 1)

theorem actualUpperRightPacketLinearEscape_iff_successorLinearEscape :
    SeamActualUpperRightPacketLinearEscape ↔
      SeamActualUpperSuccessorLinearEscape := by
  sorry

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

/-- Deliberate mismatch: the extra `True` premise must be rejected. -/
theorem actualUpperSuccessorLinearEscape_completeCounterexample
    (hescape : SeamActualUpperSuccessorLinearEscape) :
    True →
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  sorry

end

end Erdos249257.ExternalVerification257ActualUpperSuccessor
