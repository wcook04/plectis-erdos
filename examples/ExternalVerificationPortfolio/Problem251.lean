/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257
import ExternalVerification.Solution

/-!
# Erdős #251: dyadic-tail integrality classification

This downstream module exposes the exact denominator/Mersenne classifier for
an integer-digit dyadic tail, its rational-candidate specialization for the
actual consecutive-prime-gap tail, and the conditional actual-prime consumer
for a cofinal adjacent small-mismatch supply.  The supply is not proved here:
this file makes no irrationality, novelty, or priority claim for Erdős #251.
-/

namespace ExternalVerificationPortfolio.Problem251

/-! ## Denominator/Mersenne mechanism -/

#check ErdosProblems.Erdos251.tailShift_integral_iff_scaledTail
#check ErdosProblems.Erdos251.tailShift_integral_iff_den_dvd_mersenne
#check ErdosProblems.Erdos251.tailShift_integral_iff_two_pow_modEq_one
#check ErdosProblems.Erdos251.rationalPrimeGapTailShift_eventuallyIntegral

/-
For an integer-digit recurrence, the finite block identity is

`T (N+h) - T N = (2^h - 1) * T N - integer`.

Consequently a shift is integral exactly when the reduced denominator of the
current state divides the Mersenne number `2^h - 1`, equivalently when `2^h`
is congruent to `1` modulo that denominator.  If a proposed prime-gap sum is
rational, its denominator splits as `2^a * q` with `q` odd; after the power of
two has been shifted away, Euler's totient of `q` gives one fixed shift that
is integral at every later candidate-tail index.  These are exact conditional
algebraic statements, not a proof that the prime-gap sum is rational.
-/

example
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : ErdosProblems.Erdos251.DyadicTailRecurrence g T)
    (N h : ℕ) :
    ErdosProblems.Erdos251.RatIntegral
        (ErdosProblems.Erdos251.tailShift T h N) ↔
      (T N).den ∣ 2 ^ h - 1 :=
  ErdosProblems.Erdos251.tailShift_integral_iff_den_dvd_mersenne hrec N h

example (S : ℚ) :
    ∃ h, 0 < h ∧ ∃ N₀, ∀ N, N₀ ≤ N →
      ErdosProblems.Erdos251.RatIntegral
        (ErdosProblems.Erdos251.tailShift
          (ErdosProblems.Erdos251.rationalPrimeGapTailState S) h N) :=
  ErdosProblems.Erdos251.rationalPrimeGapTailShift_eventuallyIntegral S

/-! ## Actual-prime specialization -/

#check Erdos249257.ExternalVerification.primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch
#check Erdos249257.ExternalVerification.irrational_tsum_primeDyadicTerm_iff_primeGap

/-
The reusable consumer below has the actual prime-gap digit stream and the
exact rational dyadic recurrence in its hypotheses.  Its only external input
is the producer: beyond every cutoff, find adjacent shifts in `(-1, 1)` whose
corresponding consecutive prime gaps differ.  Such a pair cannot have both
shifts integral, so eventual integrality of the fixed shift is excluded.
The producer is a conditional route and remains the missing cofinal
small-mismatch input; finite event-density measurements do not replace it.
-/

example
    {T : ℕ → ℚ} (h : ℕ)
    (hrec :
      Erdos249257.ExternalVerification.DyadicTailRecurrence
        (fun n =>
          (Erdos249257.ExternalVerification.primeGap0 n : ℤ)) T)
    (hsupply : ∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < Erdos249257.ExternalVerification.tailShift T h N ∧
          Erdos249257.ExternalVerification.tailShift T h N < 1) ∧
       (-1 < Erdos249257.ExternalVerification.tailShift T h (N + 1) ∧
          Erdos249257.ExternalVerification.tailShift T h (N + 1) < 1)) ∧
      Erdos249257.ExternalVerification.primeGap0 (N + h + 1) ≠
        Erdos249257.ExternalVerification.primeGap0 (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      Erdos249257.ExternalVerification.RatIntegral
        (Erdos249257.ExternalVerification.tailShift T h N) :=
  Erdos249257.ExternalVerification
    .primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch
      h hrec hsupply

end ExternalVerificationPortfolio.Problem251
