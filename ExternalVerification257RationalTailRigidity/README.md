# Erdős #257: rational-support tail rigidity

This package compares four support-uniform consequences of a hypothetical
rational base-two Mersenne subseries value:

- the exact positive integral scaled-tail recurrence and its unboundedness;
- a uniform `ε log₂(N+1) + O(1)` bound for divisor-coverage zero windows;
- the reciprocal multiplicative-order lower bound for a reduced odd
  denominator; and
- the strict dyadic endpoint: an infinite dyadic-rational support has
  nonsummable reciprocal terms or reciprocal mass greater than one.

These are the principal rational-tail restrictions already front-loaded in
the authoritative #257 paper.  They are stronger as a family than exposing
only one recurrence identity or one denominator case.

## Mathematical boundary

Every statement is a necessary consequence of rationality.  None supplies a
contradiction for every infinite support.  The reciprocal-mass results require
their displayed summability or denominator hypotheses, the zero-window bound
does not give a support-independent additive constant, and unboundedness does
not itself exclude a rational orbit.

`Challenge.lean` imports only Mathlib and repeats the literal definitions used
by the four theorem types. `Solution.lean` transports the checked source
theorems from `RationalSupportCarrySkeleton.lean` and
`SublogDivisorCoverage.lean` without strengthening their conclusions.

## Verification

`comparator.json` selects all four declarations, uses precisely Palomar's
axiom budget, and enables NanoDa.  The deliberate-negative config selects a
same-named dyadic theorem with an extra `True` hypothesis, which Comparator
must reject as a declaration-type mismatch.

From `formal_math/erdos257_period_noncollapse`, run:

```sh
../../repo-python scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification257RationalTailRigidity/Challenge.lean \
  ExternalVerification257RationalTailRigidity/Solution.lean \
  ExternalVerification257RationalTailRigidity/NegativeSolution.lean \
  ExternalVerification257RationalTailRigidity/AxiomAudit.lean
```

Focused Lean elaboration and terminal Comparator/NanoDa replay are distinct
gates. A guarded exit `75` means validation was capacity-deferred, not that a
theorem failed.

## Palomar disposition

This is a coherent high-significance candidate because it packages the main
support-uniform rationality constraints rather than a quota-selected fragment.
Submission still requires exact public-source identity and terminal positive
acceptance plus deliberate-negative rejection receipts.  This directory does
not itself perform a registry submission or novelty ruling.
