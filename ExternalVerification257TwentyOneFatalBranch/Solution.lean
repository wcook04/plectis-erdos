/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TwentyOneQuotientGreedy

/-!
# Source transport for the #257 denominator-21 fatal branch

The definitions below are transparent aliases of the source-current objects.
The five proofs transport the exact source theorems without strengthening the
fatal-branch boundary into a membership claim.
-/

namespace Erdos249257.ExternalVerification257TwentyOneFatalBranch

noncomputable section

abbrev mersenneWeightRat := Erdos249257.mersenneWeightRat
noncomputable abbrev mersenneWeight := Erdos249257.mersenneWeight
noncomputable abbrev mersenneTail := Erdos249257.mersenneTail
noncomputable abbrev positiveMersenneSupportValue :=
  Erdos249257.positiveMersenneSupportValue
abbrev mersenneAchievementSet := Erdos249257.mersenneAchievementSet
noncomputable abbrev greedyMersenneRemainder :=
  Erdos249257.greedyMersenneRemainder
noncomputable abbrev greedyMersenneSupport :=
  Erdos249257.greedyMersenneSupport
noncomputable abbrev greedyMersenneSkippedSupport :=
  Erdos249257.greedyMersenneSkippedSupport
abbrev GreedyMersenneFatalAt := Erdos249257.GreedyMersenneFatalAt
abbrev weightedBoolSum :=
  Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum
abbrev integerGreedyBits :=
  Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits
abbrev integerGreedyRemainder :=
  Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder
abbrev localMersenneQuotient := Erdos249257.localMersenneQuotient
abbrev localPrefixQuotient := Erdos249257.localPrefixQuotient
abbrev endpointDivisorContribution :=
  Erdos249257.endpointDivisorContribution
abbrev localMersenneWeightsFrom :=
  Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom
abbrev localMersenneWeights :=
  Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights
abbrev lowerSupportFromBits :=
  Erdos249257.BooleanMobiusGreedyReduction.lowerSupportFromBits
abbrev twentyOneQuotientTarget := Erdos249257.twentyOneQuotientTarget
abbrev rationalMersenneGreedyBitsFrom :=
  Erdos249257.rationalMersenneGreedyBitsFrom
abbrev twentyOneEvenQuotientGreedySupport :=
  Erdos249257.twentyOneEvenQuotientGreedySupport
abbrev twentyOneEvenQuotientGreedyRemainder :=
  Erdos249257.twentyOneEvenQuotientGreedyRemainder
abbrev localPrefixTwoStepPulse := Erdos249257.localPrefixTwoStepPulse
abbrev twentyOneTargetTwoStepPulse :=
  Erdos249257.twentyOneTargetTwoStepPulse
abbrev TwentyOneClosedLowerStateSupply :=
  Erdos249257.TwentyOneClosedLowerStateSupply
abbrev TwentyOneGreedyEventuallyHitsDoublingBlocks :=
  Erdos249257.TwentyOneGreedyEventuallyHitsDoublingBlocks
abbrev TwentyOneFatalAlignedBranch :=
  Erdos249257.TwentyOneFatalAlignedBranch

theorem twentyOneClosedRow_forces_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen : bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hclosed : s ≤ 2 ^ R) :
    bits = integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) ∧
      s = twentyOneEvenQuotientGreedyRemainder R :=
  Erdos249257.twentyOneClosedRow_forces_quotientGreedy
    hlen hrow hclosed

theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  Erdos249257.one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    hsupply

theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch :=
  Erdos249257.one_div_twenty_one_mem_iff_not_fatalAlignedBranch

theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R :=
  Erdos249257.twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    hbranch

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
            (2 ^ (R + 1) + 1) :=
  Erdos249257.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    hbranch

end

end Erdos249257.ExternalVerification257TwentyOneFatalBranch
