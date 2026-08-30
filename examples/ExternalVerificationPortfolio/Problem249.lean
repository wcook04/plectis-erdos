/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257
import ExternalVerification.Solution

/-!
# Erdős #249: actual-LCM orbit separation

This downstream module exposes one endpoint-facing conditional route from the
Comparator corpus.  The source compares the actual power-two LCM tail orbit
with an explicit normalized odd-rank raw block, and shows that a cofinal
quantitative separation of that orbit from every integer supplies the existing
signed-margin producer.  The separation supply is a premise, not a proved
property of the totient orbit; this module therefore does not claim a solution
of Erdős #249 or any novelty/priority judgment.
-/

namespace ExternalVerificationPortfolio.Problem249

/-! ## Quantitative actual-LCM separation -/

/- The canonical Comparator representative and its source-side mechanism are
   intentionally visible to a reader inspecting this reusable consumer. -/
#check Erdos249257.ExternalVerification.irrational_totientSeries_of_actualLcmOrbitSeparationSupply
#check Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix
#check Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit_sub_rawApprox_eq
#check Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.abs_actualLcmTailOrbit_sub_rawApprox_lt
#check Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawApprox_eq_half_div_fourPow
#check Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.halfWordBandAt_of_rawApprox_integerSeparation
#check Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.powerTwoActualPenultimateSignedMarginSupply_of_actualLcmOrbitSeparation

/-
At exponent `a`, the source uses `H = lcm(1, ..., 2^a)` and the actual orbit
`R_(2H) - R_H`.  Its exact tail-difference identity and elementary remainder
bound reduce the orbit to the normalized odd-rank raw block.  Separation of
that block from every integer forces the half-word band, which then feeds the
existing penultimate signed-margin producer and the totient-series
irrationality consumer.

The hard natural friction is the final cofinal quantitative separation
predicate itself: it is stronger than mere non-integrality and remains open,
as do the punctured/top-edge supply details.  No irrationality follows
without that premise, and this route makes no #249 endpoint, novelty, or
priority claim.
-/
example
    (hsupply :
      Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine
        .PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  Erdos249257.ExternalVerification
    .irrational_totientSeries_of_actualLcmOrbitSeparationSupply hsupply

end ExternalVerificationPortfolio.Problem249
