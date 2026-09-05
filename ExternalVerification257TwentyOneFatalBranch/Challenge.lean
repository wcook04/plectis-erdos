/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #257 denominator-21 fatal branch

This Mathlib-only module states five exact endpoints from the denominator-21
quotient-greedy analysis: closed-row canonicalization, the closed-state
compactness implication, the exact membership/fatal-branch dichotomy, and the
eventual strict and affine forms of the sole surviving fatal regime.

The predicates are exposed literally.  In particular, the package does not
assume that the fatal branch is impossible and therefore does not prove that
`1/21` belongs to the Mersenne achievement set.
-/

namespace Erdos249257.ExternalVerification257TwentyOneFatalBranch

noncomputable section

def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

def GreedyMersenneFatalAt (x : ℝ) (n : ℕ) : Prop :=
  mersenneTail n < greedyMersenneRemainder x n

def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0

def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega

def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2

def lowerSupportFromBits : ℕ → List Bool → Finset ℕ
  | _, [] => ∅
  | d, false :: bits => lowerSupportFromBits (d + 1) bits
  | d, true :: bits => insert d (lowerSupportFromBits (d + 1) bits)

def twentyOneQuotientTarget (M : ℕ) : ℕ :=
  2 ^ M / 21

def rationalMersenneGreedyBitsFrom : ℕ → ℕ → ℚ → List Bool
  | _, 0, _ => []
  | d, n + 1, x =>
      if mersenneWeightRat d ≤ x then
        true ::
          rationalMersenneGreedyBitsFrom (d + 1) n
            (x - mersenneWeightRat d)
      else
        false :: rationalMersenneGreedyBitsFrom (d + 1) n x

def twentyOneEvenQuotientGreedySupport (R : ℕ) : Finset ℕ :=
  lowerSupportFromBits 2
    (integerGreedyBits
      (localMersenneWeights (2 * R) R)
      (twentyOneQuotientTarget (2 * R)))

def twentyOneEvenQuotientGreedyRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) R)
    (twentyOneQuotientTarget (2 * R))

def localPrefixTwoStepPulse (D : Finset ℕ) (M : ℕ) : ℕ :=
  2 * endpointDivisorContribution D (M + 1) +
    endpointDivisorContribution D (M + 2)

def twentyOneTargetTwoStepPulse (M : ℕ) : ℕ :=
  4 * (2 ^ M % 21) / 21

def TwentyOneClosedLowerStateSupply : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    ∃ D : Finset ℕ, ∃ s : ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ R) ∧
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R) ∧
      s ≤ 2 ^ R

def TwentyOneGreedyEventuallyHitsDoublingBlocks : Prop :=
  ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
    ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧
      n ∈ greedyMersenneSupport (1 / 21 : ℝ)

def TwentyOneFatalAlignedBranch : Prop :=
  ∃ n R₀ : ℕ,
    GreedyMersenneFatalAt (1 / 21 : ℝ) n ∧
      (greedyMersenneSkippedSupport (1 / 21 : ℝ)).Finite ∧
      (∀ k : ℕ,
        n + k + 1 ∈ greedyMersenneSupport (1 / 21 : ℝ)) ∧
      (∀ R : ℕ, R₀ ≤ R →
        integerGreedyBits
            (localMersenneWeights (2 * R) (2 * R))
            (twentyOneQuotientTarget (2 * R)) =
          rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) ∧
      TwentyOneGreedyEventuallyHitsDoublingBlocks

/-- Every closed denominator-21 quotient row is the canonical greedy row,
including exact saturation at the binary boundary. -/
theorem twentyOneClosedRow_forces_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen :
      bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hclosed : s ≤ 2 ^ R) :
    bits =
        integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) ∧
      s = twentyOneEvenQuotientGreedyRemainder R := by
  sorry

/-- Closed lower states at every even depth already represent `1/21`. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  sorry

/-- Membership of `1/21` is exactly exclusion of the explicit fatal aligned
branch. -/
theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch := by
  sorry

/-- In the fatal branch, the canonical quotient remainder eventually stays
strictly above closed binary capacity. -/
theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R := by
  sorry

/-- The only remaining fatal regime eventually obeys one exact affine
support-and-remainder recurrence. -/
theorem twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      twentyOneEvenQuotientGreedySupport (R + 1) =
          insert (R + 1) (twentyOneEvenQuotientGreedySupport R) ∧
        twentyOneEvenQuotientGreedyRemainder (R + 1) =
          (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) -
            (2 ^ (R + 1) + 1) := by
  sorry

end

end Erdos249257.ExternalVerification257TwentyOneFatalBranch
