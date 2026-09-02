# Erdős #257: reciprocal-summable supports at every integer base

This directory isolates one complete support-regime theorem for independent
statement and proof replay:

> If A is an infinite set of positive exponents and
> sum a in A of 1/a converges, then, for every integer base b at least two,
> sum a in A of 1/(b^a - 1) is irrational.

No pairwise-coprimality, periodicity, density, growth, or powerful-support
hypothesis is present. The zero exponent is harmlessly normalised to zero in
both formal series.

## Mathematical and attribution boundary

Challenge.lean states the theorem with only Mathlib in its import closure.
Solution.lean transports
Erdos257PeriodNoncollapse.irrational_erdosSupportSeries_of_summable_reciprocal
from Erdos257PeriodNoncollapse/AllBaseReciprocalSupportIrrationality.lean into
the same literal type.

The proof has three load-bearing stages:

1. the existing binary LCM-prefix and Cesaro mechanism produces arbitrarily
   close positive returns of the shifted support-atom sum;
2. the pointwise inequality
   shiftedRadixAtom_sub_zero_le_two_mul_binary_sub_zero bounds every radix-b
   displacement by twice its binary displacement, uniformly in b, N, and d;
3. the exact radix recurrence
   b T_b(N) - T_b(N+1) = c_A(N+1) makes a rational scaled tail integral, so a
   strictly positive return of size less than one denominator is impossible.

Erdős (1968) proved the pairwise-coprime case for every integer base t at
least two and stated that coprimality is superfluous, without printing the
proof. The base generality is his; the removed coprimality hypothesis is the
only strengthening over his printed theorem, and this packet proves it in
every integer base by an independent Lean-checked argument. This packet
makes no theorem-priority claim and does not identify its proof with
Erdős's omitted argument.

The theorem does not cover supports with divergent reciprocal mass and does
not solve universal Erdős #257. It does cover every reciprocal-summable
support at every integer base. In particular, the standard convergence of
the reciprocal sum over the powerful integers puts every infinite powerful
support inside the theorem, without any isolated-prime-power hypothesis.

## Paper correspondence

This family has Plectis Signal 100 (25 + 25 + 20 + 15 + 15): it is the
current portfolio's strongest direct contribution, not a proof, novelty,
Palomar, replay, or submission score. The one Comparator endpoint remains the
right interface; the transfer and close-return theorems are hard subordinate
mechanisms that the paper explains rather than extra endpoints added for
count.

| Comparator endpoint | Paper | Exact result | Mechanism | Exact boundary |
|---|---|---|---|---|
| irrational_supportPowerSeries_of_summable_reciprocal | erdos-257-mersenne-support-subseries | res:reciprocal-support | sec:reciprocal-support | bdry:reciprocal-support |

The authoritative public-paper base is pinned at
[c7f752d0aec77a29ef852ddc2e805ccc38f7a609](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c7f752d0aec77a29ef852ddc2e805ccc38f7a609/paper/erdos-257-mersenne-support-subseries.tex).
That public version still omits the all-base theorem. The local staged
revision is
[ErdosProblems/papers/erdos-257-mersenne-support-subseries.patch](../ErdosProblems/papers/erdos-257-mersenne-support-subseries.patch).
It applies to that exact base and front-loads the all-base theorem, its
binary-to-radix transfer, its integer-orbit endgame, and the surviving
reciprocal-divergent boundary under the stable labels in the table. This is a
paper-authoring stage, not a claim that the authoritative paper has already
changed. After operator-authorized promotion, replace the base link with the
full commit containing those labels and mark the route live.

## Comparator surfaces

comparator.json selects exactly the final all-base irrationality theorem.
comparator-negative-mismatch.json binds NegativeSolution.lean, whose
same-named theorem has an extra True hypothesis. A supported Comparator run
must accept the positive pair and reject that deliberate declaration-type
mismatch. These files are replay inputs, not replay verdicts, Palomar
eligibility, peer review, or permission to submit anything.

From formal_math/erdos257_period_noncollapse, the source-local checks are:

    ../../repo-python scripts/lean_fast_build.py --jobs 2 \
      Erdos257PeriodNoncollapse/AllBaseReciprocalSupportIrrationality.lean \
      ExternalVerification257ReciprocalSupport/Challenge.lean \
      ExternalVerification257ReciprocalSupport/Solution.lean \
      ExternalVerification257ReciprocalSupport/NegativeSolution.lean \
      ExternalVerification257ReciprocalSupport/AxiomAudit.lean

On a supported Comparator host, run the positive and deliberate-negative
configurations through the checked-in replay actuator:

    ./scripts/verify-comparator.sh

The actuator builds the pinned Comparator toolchain, runs every configured
portfolio pair including this #257 pair, and fails unless every positive
configuration is accepted and every deliberate negative is rejected with its
named declaration mismatch. Exit 75 means that the required Linux systemd
boundary is unavailable; it is not a replay verdict. No replay outcome is
recorded merely because this route exists.

## Palomar readiness boundary

formalization.yaml is the result-specific structured record for this one
Comparator configuration. It records the all-base theorem, the exact
binary-to-radix transfer, the standard three-axiom budget, the paper labels,
and the historical attribution boundary.

This is a first-wave Palomar candidate and the portfolio's first presented
result. It is a complete infinite-support regime theorem with a clear
specialist audience, not merely a lemma beneath the still-open universal
problem. The Challenge is Mathlib-only, contains one theorem, and is well
below the preferred audit-size boundary.

The remaining gates are distinct. First, the staged source-current revision
must be promoted to the authoritative paper so the endpoint route is live.
Then publish the exact packet in a public repository at a pinned full commit
SHA and record the terminal positive/negative Comparator pair on a supported
runner. The operator has directed submission of the portfolio's strongest
exact results once those gates are satisfied. Recheck Palomar's then-current
policy and submit the exact public configuration; do not mistake any pending
stage for a negative mathematical disposition.
