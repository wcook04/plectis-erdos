/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.TwentyOneQuotientGreedy

/-!
# Source transport for the #257 denominator-21 fatal branch

The definitions below are transparent aliases of the source-current objects.
The five proofs transport the exact source theorems without strengthening the
fatal-branch boundary into a membership claim.
-/

namespace Erdos249257.ExternalVerification257TwentyOneFatalBranch

noncomputable section

abbrev mersenneWeightRat := Erdos257PeriodNoncollapse.mersenneWeightRat
noncomputable abbrev mersenneWeight := Erdos257PeriodNoncollapse.mersenneWeight
noncomputable abbrev mersenneTail := Erdos257PeriodNoncollapse.mersenneTail
noncomputable abbrev positiveMersenneSupportValue :=
  Erdos257PeriodNoncollapse.positiveMersenneSupportValue
abbrev mersenneAchievementSet := Erdos257PeriodNoncollapse.mersenneAchievementSet
noncomputable abbrev greedyMersenneRemainder :=
  Erdos257PeriodNoncollapse.greedyMersenneRemainder
noncomputable abbrev greedyMersenneSupport :=
  Erdos257PeriodNoncollapse.greedyMersenneSupport
noncomputable abbrev greedyMersenneSkippedSupport :=
  Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport
abbrev GreedyMersenneFatalAt := Erdos257PeriodNoncollapse.GreedyMersenneFatalAt
abbrev weightedBoolSum :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum
abbrev integerGreedyBits :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits
abbrev integerGreedyRemainder :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyRemainder
abbrev localMersenneQuotient := Erdos257PeriodNoncollapse.localMersenneQuotient
abbrev localPrefixQuotient := Erdos257PeriodNoncollapse.localPrefixQuotient
abbrev endpointDivisorContribution :=
  Erdos257PeriodNoncollapse.endpointDivisorContribution
abbrev localMersenneWeightsFrom :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeightsFrom
abbrev localMersenneWeights :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeights
abbrev lowerSupportFromBits :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.lowerSupportFromBits
abbrev twentyOneQuotientTarget := Erdos257PeriodNoncollapse.twentyOneQuotientTarget
abbrev rationalMersenneGreedyBitsFrom :=
  Erdos257PeriodNoncollapse.rationalMersenneGreedyBitsFrom
abbrev twentyOneEvenQuotientGreedySupport :=
  Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedySupport
abbrev twentyOneEvenQuotientGreedyRemainder :=
  Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedyRemainder
abbrev localPrefixTwoStepPulse := Erdos257PeriodNoncollapse.localPrefixTwoStepPulse
abbrev twentyOneTargetTwoStepPulse :=
  Erdos257PeriodNoncollapse.twentyOneTargetTwoStepPulse
abbrev TwentyOneClosedLowerStateSupply :=
  Erdos257PeriodNoncollapse.TwentyOneClosedLowerStateSupply
abbrev TwentyOneGreedyEventuallyHitsDoublingBlocks :=
  Erdos257PeriodNoncollapse.TwentyOneGreedyEventuallyHitsDoublingBlocks
abbrev TwentyOneFatalAlignedBranch :=
  Erdos257PeriodNoncollapse.TwentyOneFatalAlignedBranch

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
  Erdos257PeriodNoncollapse.twentyOneClosedRow_forces_quotientGreedy
    hlen hrow hclosed

theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  Erdos257PeriodNoncollapse.one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    hsupply

theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch :=
  Erdos257PeriodNoncollapse.one_div_twenty_one_mem_iff_not_fatalAlignedBranch

theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R :=
  Erdos257PeriodNoncollapse.twentyOneFatalAlignedBranch_eventually_strict_supercapacity
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
  Erdos257PeriodNoncollapse.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    hbranch

end

end Erdos249257.ExternalVerification257TwentyOneFatalBranch
