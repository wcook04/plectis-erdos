/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the actual upper-successor endpoint in Erdős #257

This module retains the literal integer greedy remainder, the actual change
of the greedy prefix at an upper transition, every pulse in the realized
right-run recurrence, and the pulse-free successor lower envelope.  The first
selected theorem identifies the terminal-packet and successor formulations.
The second propagates the successor formulation to an infinite support of
value one half and the resulting refutation of universal irrationality.

Both statements are conditional.  No successor lower envelope is constructed
here, so Erdős Problem 257 remains open.
-/

namespace Erdos249257.ExternalVerification257ActualUpperSuccessor

open Set
open scoped BigOperators

noncomputable section

/-- Exact truncated reciprocal-Mersenne weight at seam row `s`. -/
def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

/-- Integer capacity of the seam subset-sum problem. -/
def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

/-- Proper-divisor weights in decreasing greedy order. -/
def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

def seamWeights (s : ℕ) : List ℕ := seamWeightsFrom s 2

def weightedBoolSum : List ℕ → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | w :: ws, b :: bs => (if b then w else 0) + weightedBoolSum ws bs

/-- Descending Boolean greedy word. -/
def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

/-- The actual integer greedy remainder at seam row `s`. -/
def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)

/-- Quotient pulse contributed by rank `d` between consecutive seam rows. -/
def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)

def seamGreedyBits (s : ℕ) : List Bool :=
  integerGreedyBits (seamWeights s) (seamSubsetTarget s)

def seamGreedyBit (s d : ℕ) : Bool :=
  (seamGreedyBits s).getD (d - 2) false

def seamBelowPulse (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if seamGreedyBit s (i + 2) then rowPulse s (i + 2) else 0

/-- The two fields of the actual adjacent cut used by the realized-run
producer.  Prefix change is the concrete upper-transition test. -/
structure SeamAdjacentCutView where
  successorCarries : Prop
  belowPulse : ℕ

def seamAdjacentCut (s : ℕ) (_hs : 5 ≤ s) : SeamAdjacentCutView where
  successorCarries :=
    (seamGreedyBits (s + 1)).take (s - 2) ≠ seamGreedyBits s
  belowPulse := seamBelowPulse s

/-- Complete affine charge accumulated over a realized right run. -/
def affineRightRunCharge (pulse : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 4 * affineRightRunCharge pulse k + pulse k + 4

/-- Terminal-packet lower envelope on literal upper/right runs. -/
def SeamActualUpperRightPacketLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    4 ^ k * (2 * (d + k)) ≤
      seamIntegerGreedyRemainder (d + k + 1) +
        affineRightRunCharge
          (fun q ↦
            (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k

/-- Pulse-free lower envelope at the immediate successor of the upper reset. -/
def SeamActualUpperSuccessorLinearEscape : Prop :=
  ∀ (d k : ℕ) (hd5 : 5 ≤ d), 13 ≤ d → k ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
    (∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) →
    2 ^ (d + 1) - 2 ^ (d - k + 1) + 2 * (d + k) ≤
      seamIntegerGreedyRemainder (d + 1)

/-- Exact cancellation of the upper reset and its realized right-run charge. -/
theorem actualUpperRightPacketLinearEscape_iff_successorLinearEscape :
    SeamActualUpperRightPacketLinearEscape ↔
      SeamActualUpperSuccessorLinearEscape := by
  sorry

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

/-- Complete problem-level consequence of the actual successor producer. -/
theorem actualUpperSuccessorLinearEscape_completeCounterexample
    (hescape : SeamActualUpperSuccessorLinearEscape) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  sorry

end

end Erdos249257.ExternalVerification257ActualUpperSuccessor
