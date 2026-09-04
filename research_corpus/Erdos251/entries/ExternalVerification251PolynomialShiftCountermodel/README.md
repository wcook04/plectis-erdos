# Erdős #251: an exact polynomial-shift countermodel

This directory isolates one exact infinite strategy-elimination theorem for
independent statement and proof replay. The single compared declaration proves
all of the following together:

> The quadratic word `g n = 2(n^2+4n+2)` is positive, even, and strictly
> increasing; with `T n = 2(n+4)^2` it satisfies
> `T (n+1) = 2 T n - g (n+1)`; every fixed shift `T (N+h)-T N` is integral;
> and every adjacent digit difference avoids `±2`.

The all-shifts clause is the consumer-facing consequence of the source theorem
that every orbit state is integral. Its significance comes from being combined
with the recurrence and the full coarse gap profile. In the source development,
the orbit is paired with

```text
g n = 2(n^2 + 4n + 2),
```

which is positive, even, polynomially growing, strictly increasing, unbounded,
and nonperiodic, and satisfies the exact dyadic recurrence
`T (n+1) = 2 T n - g (n+1)`. Its adjacent differences are `4n+10`, hence never
`±2`. The complete construction therefore proves that positivity, parity,
polynomial growth, unboundedness, nonperiodicity, and the recurrence cannot by
themselves force a nonintegral tail shift or the adjacent-small-mismatch
producer used in the current #251 route.

This is not the actual prime-gap word. It neither refutes the producer measured
in the actual primes nor proves or disproves the irrationality of the prime-gap
dyadic series. Its exact force is to rule out a broad class of coarse-input
arguments: any successful proof must use genuinely consecutive-prime
arithmetic, external fractional-tail control, or a different mechanism.

## Source and Comparator boundary

The proof-bearing source is
`ErdosProblems/Erdos251/PrimeGapDyadicTail.lean` at commit
`9eb76529a54cd7f0b873ee33ae1f54749ff819ab`, with source SHA-256
`d284ca394ba94d6e43b2819757ce27eb86562949b525f8bbf81546d613abfcd1`.
The compared theorem `polynomialGapTailCountermodel` is assembled from the
source declarations `polynomialTailOrbit_recurrence`, `polynomialGapWord_pos`,
`polynomialGapWord_even`, `polynomialGapWord_strictMono`,
`polynomialTailOrbit_shift_integral`, and
`polynomialGapWord_no_adjacent_two_digit`. Thus Comparator sees the coherent
mechanism-elimination statement itself, not a trivial endpoint detached from
its significance.

`Challenge.lean` imports only Mathlib and restates the five elementary
definitions needed by the theorem. `Solution.lean` assembles six checked source
theorems into that literal composite type. `comparator.json` selects exactly
this one complete countermodel theorem. The deliberate-negative configuration binds
`NegativeSolution.lean`, whose same-named theorem adds an irrelevant `True`
hypothesis; Comparator must reject it as a declaration-type mismatch.

From `formal_math/erdos257_period_noncollapse`, the source-local checks are:

```sh
../../repo-python scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification251PolynomialShiftCountermodel/Challenge.lean \
  ExternalVerification251PolynomialShiftCountermodel/Solution.lean \
  ExternalVerification251PolynomialShiftCountermodel/NegativeSolution.lean \
  ExternalVerification251PolynomialShiftCountermodel/AxiomAudit.lean
```

The checked-in positive and deliberate-negative configurations are replay
inputs, not replay verdicts. A supported Comparator run must accept the positive
pair and reject the negative pair with the named declaration mismatch. Until
that terminal pair is recorded, no Comparator acceptance is claimed.

The Challenge, proof-bearing Solution, deliberate-negative fixture, and axiom
audit all pass focused local Lean elaboration. The composite theorem depends
exactly on `propext`, `Classical.choice`, and `Quot.sound`, within the declared
Comparator trust budget. This Lean-kernel evidence does not replace the
still-pending Comparator replay.

## Palomar candidacy

This is a Palomar candidate: a source-independent, one-theorem, exact infinite
countermodel that eliminates a broad and natural strategy for an open Erdős
problem. Its research interest is the sharp separation it proves—the actual
cofinality argument must see arithmetic that the explicitly listed coarse gap
profile forgets—not the elementary appearance of any one conjunct.

Submission readiness still requires this object at a pinned public full
commit, terminal positive acceptance and deliberate-negative rejection from
Comparator on a supported host, and current result-level metadata and licence
evidence. The operator has directed a Palomar submission campaign for the
portfolio's strongest results; the exact public commit and configuration still
have to be fixed before the outbound act. These are mechanical and identity
gates, not a negative judgment about the result's mathematical value.
