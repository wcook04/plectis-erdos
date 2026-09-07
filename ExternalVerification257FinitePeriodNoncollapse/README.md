# Erdős #257: unconditional finite-period noncollapse

This directory isolates the strongest finite-support denominator family in
the current Erdős #257 programme as two source-independent Comparator results.
For every finite nonempty set `F` of positive exponents and every integer base
`b ≥ 2`, write

\[
S_F(b)=\sum_{n\in F}\frac{1}{b^n-1}=\frac{P}{Q}
\]

in lowest terms. The two compared results jointly prove that

- `gcd(b,Q)=1`;
- the multiplicative order of `b` modulo `Q` is exactly `lcm(F)`;
- if `lcm(F) ≥ 2`, then `lcm(F) < Q`.

The result is unconditional: the proof constructs the exact-order prime-power
witnesses needed to survive denominator reduction.  It is uniform in the
base and support, not a bounded computation or a finite certificate table.

## Mathematical boundary

The theorem concerns finite support.  It proves that every finite partial sum
retains its full cyclotomic period and gives a strict denominator lower bound;
it does not convert that growth into irrationality for an arbitrary infinite
support.  Erdős #257 therefore remains open in its universal form.

`Challenge.lean` imports only Mathlib and defines only the literal rational
sum.  `Solution.lean` transports three checked source endpoints from
`Erdos257PeriodNoncollapse.CertificateKernel`: reduced-denominator
coprimality, exact multiplicative order, and strict denominator growth.

## Verification

`comparator.json` selects the complete two-theorem family: existential
coprimality-plus-exact-order production, followed by strict denominator
growth. This preserves the source theorem boundary instead of hiding the
growth endpoint inside a conditional conjunction.
`comparator-negative-mismatch.json` points to same-named declarations with an
extra `True` hypothesis, which Comparator must reject as type mismatches.

From `formal_math/erdos257_period_noncollapse`, focused Lean checks are:

```sh
./scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification257FinitePeriodNoncollapse/Challenge.lean \
  ExternalVerification257FinitePeriodNoncollapse/Solution.lean \
  ExternalVerification257FinitePeriodNoncollapse/NegativeSolution.lean \
  ExternalVerification257FinitePeriodNoncollapse/AxiomAudit.lean
```

The checked-in replay actuator runs the positive and deliberate-negative
configurations on a supported Linux host.  Exit `75` is an environment
unavailability receipt, not a Comparator verdict.

The source-aligned two-theorem Challenge, proof-bearing Solution,
deliberate-negative fixture, and AxiomAudit all pass focused local Lean
elaboration. Both compared theorems report exactly `propext`,
`Classical.choice`, and `Quot.sound`. Supported terminal Comparator/NanoDa
replay remains a separate gate.

## Palomar disposition

This is a first-wave Palomar candidate.  Exact finite-period survival under
reduction, uniformly for every base and finite positive support, is a coherent
research-note result with a number-theory and formal-mathematics audience.  The
open infinite-support parent problem is an honest boundary, not a reason to
withhold this theorem.

Submission still requires a public GitHub repository at a full immutable
commit SHA, this exact config path, terminal positive acceptance, deliberate
negative rejection, and source-current metadata.  These local files are not a
Palomar decision, registry entry, novelty ruling, or peer review.
