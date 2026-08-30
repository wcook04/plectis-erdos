# External verification portfolio

This directory contains small Lean consumers for six different parts of the
Erdős 68/243/249/251/257/269 corpus. The files are useful when a reader wants to reuse
an exact Comparator-facing interface without treating a conditional reduction
as a solution of the underlying Erdős problem.

The canonical focused check for the portfolio consumers is:

```bash
python3 scripts/lean_fast_build.py \
  examples/ExternalVerificationPortfolio/Problem68.lean \
  examples/ExternalVerificationPortfolio/Problem243.lean \
  examples/ExternalVerificationPortfolio/Problem249.lean \
  examples/ExternalVerificationPortfolio/Problem251.lean \
  examples/ExternalVerificationPortfolio/Problem257.lean \
  examples/ExternalVerificationPortfolio/Problem269.lean
```

That command imports the shared `ExternalVerification.Solution` surface. A
consumer is Lean-green only when its exact focused source check reaches a
successful terminal result on the current checkout; a dependency-bootstrap
or capacity deferral is not theorem evidence and must not be reported as a
theorem failure or a passing check.

## Erdős #68: two equivalent endpoint coordinates

[`Problem68.lean`](Problem68.lean) exposes two exact Comparator-facing
characterizations of the factorial-gap series.  The first says that its
irrationality is equivalent to cofinally many indices `m` at which
`m` does not divide
`strictFacTopRat (factorialGapPrefix m) m`.  The second says equivalently that
the exact strict-successor carry `factorialGapStepCarry m` is different from
one cofinally often.

These are two coordinates on the same endpoint, not two independent routes.
For every `m ≥ 3`, the source theorem
`factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat` identifies a unit carry
with the corresponding divisibility event.  Rationality forces eventual unit
carries, while eventual unit carries conversely make the normalized
strict-factorial successors stationary.  The exact endpoint sources are in
[`FactorialZeroPlateau.lean`](../../ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L856).

The missing input is a cofinal producer for either equivalent right-hand
side.  Exact misses or nonunit carries at finitely many computed indices can
raise lower bounds on a displayed rational denominator, but cannot discharge
the quantifier `∀ B, ∃ m > B`.  This consumer therefore proves no #68
irrationality and makes no novelty or priority claim.

## Erdős #243: two conditional recovery criteria

[`Problem243.lean`](Problem243.lean) keeps two source-faithful recovery
criteria distinct.  Neither supplies the missing hypotheses for an
unrestricted reciprocal-tail orbit, so neither is a solution or an
irrationality claim for #243.

### Bounded negative part

The exact external wrapper is
`Erdos249257.ExternalVerification.boundedNegativePart_eventually_zero`.
It takes natural `a`, `C`, and `D`, an integral centered defect `E`, and the
exact `C/D/E` dynamics: `C (n + 1) + D n = a n * C n`,
`D (n + 1) = a n * D n`, and `E n` is the centered state.  Strict centering,
a uniform lower bound on `E`, and division-free normalized vanishing yield
eventual `E = 0`.  Its source is
[`ReciprocalTailRigidity.lean`](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2265).

The unbounded and mixed-sign branches are not discharged by this wrapper:
the route still needs an actual-orbit producer for the lower-bound/vanishing
package.  In particular, no prime-specific input is asserted to produce it.

### Summable normalized negative mass

The stronger endpoint is
`Erdos249257.ExternalVerification.sylvesterNext_eventually_of_summable_negativeRelativeMass`.
It preserves the exact `nextDenState` and `nextTailState` recurrence, positive
natural tail `C`, the centered step equation, and normalized vanishing; its
additional premise is summability of the normalized negative mass.  The
conclusion is eventual Sylvester recurrence, not an unconditional recurrence
for reciprocal-tail data.  Its source is
[`SparseResetRecovery.lean`](../../ErdosProblems/Erdos243/SparseResetRecovery.lean#L175).

The missing producer is correspondingly stronger: neither the mixed-sign
analysis nor a prime-specific negative-mass supply proves the required
summability.  The defect identity, zero-absorption lemma, and fresh-modulus
bounded-rise obstruction are reusable supporting mechanisms, not equal
headlines or extra #243 endpoint claims.  This consumer makes no #243
irrationality, novelty, or priority claim.

## Erdős #257: ranked structured-support frontier

Start with [`Problem257.lean`](Problem257.lean). It calls four distinct public
`ExternalVerification` wrappers in Palomar order. The first three are
unconditional theorems for stated structured classes; the fourth is a
conditional reduction. None proves irrationality for every infinite support,
and none should be read as a universal solution of #257.

### Full support

The exact wrapper is
`Erdos249257.ExternalVerification.irrational_erdosSum_full_support`, with the
single hypothesis `b : ℕ` and `2 ≤ b`. Its source is
[`CertificateKernel.lean`](../../Erdos249257/CertificateKernel.lean#L8328).
The hard mechanism is a completed weighted divisor-block certificate: a
Bertrand/CRT first block, divisor-pair averaging in a middle window, and
explicit tail closure. The conclusion is for the full-support
Erdős--Borwein series only; arbitrary infinite support remains outside the
theorem.

### Pairwise-coprime support

The exact wrapper is
`Erdos249257.ExternalVerification.irrational_erdosSupportSeries_pairwise_coprime`.
It requires `b : ℕ` with `2 ≤ b`, `A : Set ℕ` with `A.Infinite`,
`A.Pairwise Nat.Coprime`, and
`Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a))`. Its source is
[`CertificateKernel.lean`](../../Erdos249257/CertificateKernel.lean#L10776).
Adaptive CRT absorbs small support elements at residue zero, block sizes absorb
their deterministic hits, and summable reciprocal mass controls the strays.
The pairwise-coprime and summability hypotheses are essential: this is not an
arbitrary-support theorem or the universal #257 claim.

### Nonnegative eventually-periodic rational weights

The exact wrapper is
`Erdos249257.ExternalVerification.irrational_ratWeightSeries_eventuallyPeriodic`.
It requires `b m N₀ : ℕ`, `γ : ℕ → ℚ`, `2 ≤ b`, `0 < m`, pointwise
`0 ≤ γ n`, eventual periodicity `γ (n + m) = γ n` for every `n ≥ N₀`, and
some `a` with `N₀ ≤ a`, `0 < a`, and `0 < γ a`. Its source is
[`CertificateKernel.lean`](../../Erdos249257/CertificateKernel.lean#L12811).
The mechanism clears one common denominator on the prefix-plus-period window,
reduces to an eventually-periodic natural weight, and applies the weighted
certificate argument. Mixed-sign weights and arbitrary supports are outside
the result; this remains a structured-family theorem, not universal #257.

### Orthogonal petals: conditional route

The exact wrapper is
`Erdos249257.ExternalVerification.irrational_erdosSupportSeries_of_orthogonalPetalBouquet`.
It takes both `OrthogonalPetalBouquet A` and
`SunflowerForcedSlotTailSelection A`, at base `2`. The bouquet hypothesis
includes a positive finite-core modulus `Q`; positive exceptional divisors of
`Q`; positive cores dividing `Q`; petals greater than one, individually
coprime to `Q`, and pairwise coprime; exact support equality by the exceptional
frame and core-times-petal rays; and summable reciprocal petal mass. The
selector requires, for every `K > 0`, a starting point `N` whose first `K`
support-coefficient block is divisible by `2^K` and whose binary coefficient
tail is at most `16`. The source route is
[`SupportSunflowerDichotomy.lean`](../../Erdos249257/SupportSunflowerDichotomy.lean#L540).
Its hard mechanism is the finite-core divisor/frame decomposition and bounded
petal tail budget, but the selector is not proved. This is therefore a
conditional support route, not an unconditional family, universal #257 result,
or novelty claim.

## Erdős #249: actual-LCM orbit separation

Start with [`Problem249.lean`](Problem249.lean). Its load-bearing Comparator
wrapper is
`Erdos249257.ExternalVerification.irrational_totientSeries_of_actualLcmOrbitSeparationSupply`.
The wrapper says that the totient series is irrational under the explicit
`PowerTwoActualLcmOrbitSeparationSupply` premise; it does not prove that
premise.

The source route is split across:

- [`Erdos249257/DiagonalFreshLossBridge.lean`](../../Erdos249257/DiagonalFreshLossBridge.lean), which defines the actual power-two LCM orbit, the normalized odd-rank raw block, and the bridge identities;
- [`Erdos249257/TotientActualLcmOrbitSeparation.lean`](../../Erdos249257/TotientActualLcmOrbitSeparation.lean), which gives the exact tail-difference, remainder, half-word-band, signed-margin, and conditional irrationality route;
- [`ExternalVerification/Solution.lean`](../../ExternalVerification/Solution.lean), which exposes the Comparator wrapper used by the portfolio consumer.

The hard step is the reduction from the orbit
`R_(2H) - R_H` to the normalized odd-rank raw block, followed by the
cofinal quantitative separation from every integer that forces the
half-word band and feeds the penultimate signed-margin producer. The natural
friction is at the last step: quantitative cofinal separation is stronger
than saying that an orbit is sometimes nonintegral, and the required supply,
including the punctured/top-edge details, remains open. Without that supply
there is no #249 irrationality conclusion, and this consumer makes no
novelty or priority claim.

## Erdős #251: dyadic-tail integrality classification

Start with [`Problem251.lean`](Problem251.lean). Its load-bearing source
interfaces are
`ErdosProblems.Erdos251.tailShift_integral_iff_den_dvd_mersenne`,
`ErdosProblems.Erdos251.tailShift_integral_iff_two_pow_modEq_one`, and
`ErdosProblems.Erdos251.rationalPrimeGapTailShift_eventuallyIntegral`; the
actual-prime Comparator specialization is
`Erdos249257.ExternalVerification.primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch`.

The exact mechanism is elementary and conditional. For an integer-digit
dyadic recurrence, the `h`-step shift is an integer exactly when the reduced
denominator of the current tail state divides the Mersenne number `2^h - 1`,
equivalently when `2^h ≡ 1` modulo that denominator. A rational candidate
prime-gap sum has denominator `2^a q` with `q` odd; after the power-of-two
part is shifted out, Euler's totient of `q` supplies a fixed shift that is
eventually integral along the candidate tail.

The actual-prime consumer says what would finish this route: if, for one fixed
shift `h`, every cutoff admits an adjacent pair of tail shifts both strictly
inside `(-1,1)` with unequal corresponding consecutive prime gaps, then that
shift cannot be eventually integral. The missing input is precisely that
cofinal small-mismatch producer for the actual primes (or a different
actual-tail obstruction). Finite event-density measurements do not supply the
cofinal quantifier. This consumer therefore proves no #251 irrationality and
makes no novelty or priority claim.

## Erdős #269: two distinct reusable routes

[`Problem269.lean`](Problem269.lean) keeps the weighted observer and the
conditional carry escape separate.

### Weighted phase observer

The exact Comparator interface is
`Erdos249257.ExternalVerification.carry_eq_residueDigit_add_coboundary`.
Its source is [`ErdosProblems/Erdos269/WeightedPhaseCarry.lean`](../../ErdosProblems/Erdos269/WeightedPhaseCarry.lean), with the finite residue and digit interval checks and the
`finite_realisedSpan_of_factorisation` observer consequence. The recurrence
is decomposed into a finite residue digit and an integral quotient coboundary,
which is the useful reusable mechanism.

The finite residue is not a finite-state quotient recurrence: the quotient
coboundary remains uncontrolled, and finite realised span requires an explicit
finite-dimensional, function-faithful factorisation. A scalar evaluation does
not prove that factorisation. The actual three-prime running-LCM bridge and a
cofinal escape producer are still open, so this route proves no #269
rationality or irrationality statement.

### Conditional carry escape

The exact Comparator interface is
`Erdos249257.ExternalVerification.no_positive_reducedCarry_of_cofinalLocalWindowEscape`.
Its source is [`ErdosProblems/Erdos269/RestrictedFloorSum.lean`](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean), which consumes
`CofinalLocalWindowEscape` together with positive, coprime multiplier data,
the exact integer carry recurrence, and the denominator-dependent short bound
to derive `False`.

The difficult input is precisely the one the consumer assumes: a cofinal
local-window residue escape, together with a bridge from the actual
three-prime running-LCM series or its rationality to this reduced carry. Those
inputs are not proved here. This is therefore a conditional obstruction, not
an unconditional #269 endpoint, irrationality proof, novelty claim, or
priority claim. The finite block alphabet and rank-two kernel routes remain
supporting or contrary evidence rather than extra portfolio families.

For the configured interfaces and their recorded evidence boundaries, see
[`verification/comparator.json`](../../verification/comparator.json) and the
exact source consumers above. The #249, #251, #257, and #269 examples are
deliberately separate: #249 consumes an actual-LCM separation supply, #251
consumes the dyadic-tail denominator classifier and an actual-prime mismatch
obstruction, #257 separates four support/weight classes with distinct
hypotheses, and #269 exposes a residue/coboundary mechanism plus a local-window
carry consumer. Their hypotheses and open bridges differ.
