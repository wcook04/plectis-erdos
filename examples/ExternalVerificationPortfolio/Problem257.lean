/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257
import ExternalVerification.Solution

/-!
# Erdős #257: the ranked structured-support frontier

This downstream module gives a cold reader four distinct, reusable
Comparator-facing routes for the Mersenne support series.  The first three
are unconditional structured-family theorems; the fourth is a conditional
orthogonal-petal reduction.  None of these families proves the universal
claim for every infinite support.

The examples below deliberately apply the public `ExternalVerification`
wrappers rather than importing a proof-local declaration.  Their comments
keep the hypotheses, mechanism, and surviving open boundary beside the
typed consumer.
-/

namespace ExternalVerificationPortfolio.Problem257

open Erdos249257.ExternalVerification

/-! ## Full support: the classical benchmark

The exact hypothesis is only an integer base `b` with `2 ≤ b`.  The checked
source route is the finite block-certificate engine in
`Erdos249257/CertificateKernel.lean:8328`: a Bertrand/CRT first block,
divisor-pair averaging in a middle window, and explicit tail closure.  This
is the full-support Erdős--Borwein theorem, not the universal #257 claim.
-/

#check Erdos249257.ExternalVerification.irrational_erdosSum_full_support
#check Erdos249257.irrational_erdosSum_full_support

example (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) :=
  Erdos249257.ExternalVerification.irrational_erdosSum_full_support b hb

/-! ## Pairwise-coprime support: adaptive non-dilation

For `b : ℕ`, `A : Set ℕ`, the wrapper keeps every hypothesis explicit:
`2 ≤ b`, `A.Infinite`, pairwise coprimality of elements of `A`, and
summability of the reciprocal indicator `1/a`.  The source theorem at
`Erdos249257/CertificateKernel.lean:10776` uses an adaptive CRT modulus:
small support elements are absorbed at residue zero, block sizes absorb their
deterministic hits, and summable reciprocals control the strays.  It does
not cover arbitrary infinite supports, and none of these hypotheses may be
silently inferred from the #257 statement.
-/

#check Erdos249257.ExternalVerification.irrational_erdosSupportSeries_pairwise_coprime
#check Erdos249257.irrational_erdosSupportSeries_pairwise_coprime

example (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    Irrational (erdosSupportSeries b A) :=
  Erdos249257.ExternalVerification.irrational_erdosSupportSeries_pairwise_coprime
    b A hb hA hpair hsum

/-! ## Eventually-periodic nonnegative rational weights

The exact data are a base `b`, period `m`, threshold `N₀`, and rational
weights `γ : ℕ → ℚ`, with `2 ≤ b`, `0 < m`, pointwise `0 ≤ γ n`, eventual
periodicity `γ (n + m) = γ n` for `N₀ ≤ n`, and a positive weight at some
positive index in the periodic region.  The hard step in
`Erdos249257/CertificateKernel.lean:12811` clears one common denominator on
the prefix-plus-period window, reduces to an eventually-periodic natural
weight, and applies the weighted certificate argument.  Mixed-sign periodic
weights are outside this theorem; it is a structured-family result, not the
universal #257 statement.
-/

#check Erdos249257.ExternalVerification.irrational_ratWeightSeries_eventuallyPeriodic
#check Erdos249257.irrational_ratWeightSeries_eventuallyPeriodic

example (b m N₀ : ℕ) (γ : ℕ → ℚ) (hb : 2 ≤ b) (hm : 0 < m)
    (hγ0 : ∀ n : ℕ, 0 ≤ γ n)
    (hper : ∀ n : ℕ, N₀ ≤ n → γ (n + m) = γ n)
    (hpos : ∃ a : ℕ, N₀ ≤ a ∧ 0 < a ∧ 0 < γ a) :
    Irrational (∑' a : ℕ, ((γ a : ℝ)) / ((b : ℝ) ^ a - 1)) :=
  Erdos249257.ExternalVerification.irrational_ratWeightSeries_eventuallyPeriodic
    b m N₀ γ hb hm hγ0 hper hpos

/-! ## Orthogonal petals: a conditional route with an open selector

The wrapper requires both `OrthogonalPetalBouquet A` and
`SunflowerForcedSlotTailSelection A`.  The bouquet hypothesis includes all
of its structural data: a positive finite-core modulus `Q`; positive
exceptional elements dividing `Q`; positive cores dividing `Q`; petals
strictly greater than one, individually coprime to `Q`, and pairwise
coprime; exact support equality with the exceptional frame plus the core
times petal rays; and summable reciprocal petal mass.  The selector requires
for every `K > 0` a starting point `N` whose first `K` support-coefficient
block is divisible by `2^K` and whose binary coefficient tail is at most
`16`.

The source route at
`Erdos249257/SupportSunflowerDichotomy.lean:540` converts that selector to
the forced-carry certificate and hence irrationality at base `2`.  Its hard
mechanism is the finite-core divisor/frame decomposition plus the bounded
petal tail budget.  The selector is not proved, so this is not an
unconditional support family, a universal #257 result, or a novelty claim.
-/

#check Erdos249257.ExternalVerification.irrational_erdosSupportSeries_of_orthogonalPetalBouquet
#check Erdos249257.SupportSunflowerDichotomy.OrthogonalPetalBouquet
#check Erdos249257.SupportSunflowerDichotomy.SunflowerForcedSlotTailSelection
#check Erdos249257.SupportSunflowerDichotomy.irrational_erdosSupportSeries_of_orthogonalPetalBouquet

example {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (hselection : SunflowerForcedSlotTailSelection A) :
    Irrational (erdosSupportSeries 2 A) :=
  Erdos249257.ExternalVerification.irrational_erdosSupportSeries_of_orthogonalPetalBouquet
    hB hselection

end ExternalVerificationPortfolio.Problem257
