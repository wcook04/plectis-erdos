# Erdős #257: supported Mersenne achievement-set geometry

This package isolates one coherent source-independent Comparator theorem for
every allowed set `J` of binary Mersenne coordinates. It simultaneously
asserts that the supported digit map is injective, its range is compact and
nowhere dense, the range is perfect when `J` is infinite, and its Lebesgue
measure has the exact dichotomy

\[
  \operatorname{vol}(K_J)=
  \begin{cases}
    2^{-|F|}, & J=\mathbb N\setminus F\text{ for a finite }F,\\
    0, & \mathbb N\setminus J\text{ is infinite}.
  \end{cases}
\]

The theorem captures the full support-uniform achievement-set family rather
than selecting only the full-support volume theorem or only the null branch.

## Mathematical boundary

`Challenge.lean` imports only Mathlib and repeats the literal definitions of
the Mersenne weight, digit term, positive digit value, supported digit type,
restricted digit map, and supported achievement set. `Solution.lean` assembles
the checked source declarations from
`ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean`.

The theorem classifies geometry and Lebesgue measure. It does not assert that
every infinite supported sum is irrational and does not solve universal
Erdős #257. Perfection requires `J.Infinite`; compactness, nowhere density,
injectivity, and the volume dichotomy hold for every `J`.

## Verification

`comparator.json` selects the single composite theorem with the standard
Palomar axiom budget and NanoDa enabled. The deliberate-negative configuration
uses `NegativeSolution.lean`, whose same-named theorem has an extra `True`
hypothesis and therefore must be rejected as a declaration-type mismatch.

From `formal_math/erdos257_period_noncollapse`, run:

```sh
../../repo-python scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification257AchievementSetGeometry/Challenge.lean \
  ExternalVerification257AchievementSetGeometry/Solution.lean \
  ExternalVerification257AchievementSetGeometry/NegativeSolution.lean \
  ExternalVerification257AchievementSetGeometry/AxiomAudit.lean
```

Focused Lean elaboration is distinct from terminal Comparator replay. A local
exit `75` means validation was capacity-deferred, not that the theorem failed.
Supported positive acceptance and deliberate-negative rejection remain
identity-bound replay gates.

## Palomar disposition

This is a coherent candidate package: one support-uniform theorem combines
the central coding, topology, and exact measure classification, while the
Challenge remains Mathlib-only and auditable. Submission still requires an
exact public repository commit, terminal positive and negative replay
receipts, and source-current metadata. Nothing in this directory is itself a
Palomar decision, registry entry, novelty ruling, or peer review.
