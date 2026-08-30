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
      Erdos249257.ExternalVerification.PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  Erdos249257.ExternalVerification.irrational_totientSeries_of_actualLcmOrbitSeparationSupply
    hsupply

/-! ## Natural-prime phase dynamics and strict-gap endpoint route -/

#check ErdosProblems.Erdos249.DTWNaturalPrimeTailOrbitStrictGap
#check ErdosProblems.Erdos249.tailOrbitFirstExp_zero_eq_scaled_angle
#check ErdosProblems.Erdos249.exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic
#check ErdosProblems.Erdos249.tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen
#check ErdosProblems.Erdos249.cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic
#check ErdosProblems.Erdos249.naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift
#check ErdosProblems.Erdos249.naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap
#check Erdos249257.ExternalVerification.irrational_totient_series_of_naturalPrimeTailOrbitStrictGap

/-
For a fixed positive shift `h`, the source identifies the initial actual-tail
phase exactly as

`exp (2 * pi * I * ((2^h - 1) * S))`,

where `S` is the binary totient series; every later phase is obtained by
repeated squaring.  Reaching phase `1` after finitely many squarings is
therefore equivalent to the real angle `(2^h - 1) * S` being dyadic.  The
existing exact certificate at time `14` excludes this obstruction for
`1 <= h <= 16` and root depth at most `14`, but it does not prove global
non-dyadicity.

For any fixed `h` whose angle is non-dyadic, elementary doubling geometry
gives cofinally many indices with nonpositive real phase.  This is an
anti-concentration statement in the limited sense of cofinal occurrence: it
does not give a positive block density or put those indices at shifted primes.
The theorem
`naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift` isolates
that remaining arithmetic supply: cofinally many nonpositive phases with
`N + h + 1` prime imply the existing strict prime-orbit gap.

The source also exposes a block-density route.  A
`TotientTailOrbitNonpositiveBlockDensity` hypothesis supplies an `11/100`
fraction of nonpositive phases on a late dyadic block.  Unit norm bounds the
remaining phases by `1`, so the block mean is at most `89/100`; one truncation
depth with a uniform `1/100` tail error then reaches the finite `9/10`
first-harmonic gap and an existing certified kill.

The distinct prime-index route skips the block average.  Its exact source
predicate `DTWNaturalPrimeTailOrbitStrictGap` asks, for each positive shift and
lower bound, for a prime `p` with
`Re(tailOrbitFirstExp h (p - h - 1)) < 9/10`.  The source theorem
`naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap` sets
`N = p - h - 1`, uses the prime-index equality to enter the pivot fibre, and
chooses `L` from the positive margin
`9/10 - Re(tailOrbitFirstExp h N)` to transfer the infinite-orbit gap to one
finite truncation.  The Comparator wrapper below exposes that exact
conditional endpoint beside actual-LCM separation.

The global non-dyadicity, `11/100` nonpositive-block density, and cofinal
prime-alignment supplies remain open.  In particular, cofinal nonpositive
occurrence at unrestricted indices does not imply either of the latter two
producers.  This consumer therefore makes no unconditional #249, novelty, or
priority claim.
-/
example
    (hgap : Erdos249257.ExternalVerification.DTWNaturalPrimeTailOrbitStrictGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  Erdos249257.ExternalVerification.irrational_totient_series_of_naturalPrimeTailOrbitStrictGap
    hgap

end ExternalVerificationPortfolio.Problem249
