# Erdős #68: companion orbit and strict-successor characterizations

This directory exposes the two strongest exact coordinates from the current
Erdős #68 development as one coherent Comparator package.  For the literal series

\[
S=\sum_{n\ge 2}\frac{1}{n!-1},
\]

put

\[
C=\sum_{n\ge2}\frac1{n!(n!-1)}.
\]

The strongest theorem is

- `S` is non-irrational exactly when `⌊m! C⌋ ≡ -2 (mod m)` eventually;
- `S` is irrational exactly when that exceptional residue is missed cofinally.

For the second coordinate, let `H_m` be the rational prefix, let `Z_m` be the first integer strictly
above `m! H_m`, and let the exact recurrence digit be `c_m`.  The compared
strict-successor theorem proves all of the following:

- `S` is non-irrational exactly when `c_m = 1` eventually;
- `S` is irrational exactly when `c_m ≠ 1` cofinally;
- for every `m ≥ 3`, `c_m = 1` exactly when `m ∣ Z_m`;
- hence `S` is irrational exactly when `m ∤ Z_m` cofinally.

The last line is a lossless, purely integral reformulation of the original
irrationality question.  It removes real approximation and prime
restrictions from the frontier without pretending that the remaining
cofinal-miss producer has been proved.

## Mathematical boundary

`Challenge.lean` imports only Mathlib and states both complete theorems in
literal definitions.  `Solution.lean` transports the companion-orbit endpoints
from `ErdosProblems.Erdos68.CompanionOrbitRationality`, then assembles the
independently checked carry and divisibility endpoints from the same #68 source
closure.

This result is not a proof that cofinally many misses occur.  It therefore
does not prove irrationality or solve Erdős #68.  Finite carry certificates,
denominator exclusions, continued-fraction computations, prime-pole
identities, and private-prime mechanisms remain supporting results rather
than additional claims inside this Comparator configuration.

## Comparator surfaces

`comparator.json` selects the companion-orbit theorem first and the
strict-successor theorem second.  The exact selected declarations are

- `Erdos249257.ExternalVerification68StrictSuccessorCarry.companionOrbit_completeCharacterization`;
- `Erdos249257.ExternalVerification68StrictSuccessorCarry.strictSuccessorCarry_completeCharacterization`.

`comparator-negative-mismatch.json` binds `NegativeSolution.lean`, whose
same-named theorem has an extra `True` hypothesis.  A supported Comparator run
must accept the positive pair and reject that deliberate type mismatch.

From `formal_math/erdos257_period_noncollapse`, focused source-local checks
are:

```sh
./scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification68StrictSuccessorCarry/Challenge.lean \
  ExternalVerification68StrictSuccessorCarry/Solution.lean \
  ExternalVerification68StrictSuccessorCarry/NegativeSolution.lean \
  ExternalVerification68StrictSuccessorCarry/AxiomAudit.lean
```

On a supported Linux host, `./scripts/verify-comparator.sh` runs the positive
and deliberate-negative pair.  Exit `75` means the required systemd boundary
is unavailable; it is not a Comparator verdict.  The current macOS host was
exercised through that exact entrypoint on 31 August 2026 and returned `75`, so
the terminal positive/negative replay remains assigned to a supported runner.

The Challenge, proof-bearing Solution, deliberate-negative fixture, and axiom
audit all pass focused local Lean elaboration.  Both audited theorems depend
exactly on `propext`, `Classical.choice`, and `Quot.sound`, within the declared
Comparator trust budget.  This is a Lean-kernel result, not a substitute for
the still-pending Comparator replay.

## Exact paper routes

The source-current paper is
`ErdosProblems/papers/erdos-68-factorial-denominator-irrationality.tex`.
Its cumulative public-paper patch is
`ErdosProblems/papers/erdos-68-companion-orbit-equivalence.patch`, based on the
immutable public commit and file hash recorded in the patch header.
The companion theorem routes to
`res:companion-orbit-rationality-boundary` and its exact surviving boundary to
`bdry:companion-orbit-nonconcentration`.  The strict-successor theorem routes
to `res:strict-successor-complete-characterization`.  Until the staged paper
patch and source module share a public immutable commit, these are staged
source-current labels rather than public-release coordinates.

## Palomar disposition

This configuration is a coherent but subordinate Palomar candidate.  The
canonical portfolio ledger assigns the combined exact-coordinate family
Plectis Signal 20: the fixed companion orbit comes first because it is the
cleanest coordinate, followed by the strict-successor characterization, but
neither theorem supplies the cofinal producer.  They belong in one concise
entry after #68's unconditional obstructions and conditional advances, not as
a padded top-band claim.  The fact that Erdős #68 itself remains open is part
of their honest boundary, not by itself a non-submission reason.

Submission still requires the mechanical identity Palomar records: a public
GitHub repository, full immutable commit SHA, exact config path, successful
positive replay, deliberate-negative rejection, and source-current metadata.
No local file or self-assessment is represented as a Palomar verdict, registry
entry, or peer review.
