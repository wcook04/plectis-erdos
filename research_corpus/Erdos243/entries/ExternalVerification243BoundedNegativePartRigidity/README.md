# Erdős #243: bounded-negative-part rigidity

This package isolates the complete checked theorem for the bounded-negative
centered-error branch of the Erdős #243 programme.  For exact natural
reciprocal-tail states

\[
C_{n+1}+D_n=a_nC_n,\qquad D_{n+1}=a_nD_n,
\]

write

\[
E_n=D_n-(a_n-1)C_n.
\]

Assume eventual strict centering `|Eₙ| < Cₙ`, an eventual one-sided lower
bound `-B ≤ Eₙ`, and the division-free normalized vanishing condition
`K|Eₙ| < Cₙ` eventually for every fixed `K`.  The compared theorem proves
both

- `Eₙ = 0` eventually; and
- `aₙ₊₁ = aₙ² - aₙ + 1` eventually.

This is more than a periodic-orbit exclusion.  No periodicity or eventual
periodicity assumption appears: the result covers the entire bounded-negative
regime, including aperiodic candidates.  Its proof combines two genuinely
different mechanisms.  The nonnegative branch gives descent of a natural tail
state, while recurring bounded negative errors force gcd stabilization, scale
reduction, and a shifted Chinese-remainder obstruction.

## Mathematical boundary

The theorem is conditional.  Exact dynamics, positivity, eventual strict
centering, eventual one-sided boundedness, and normalized vanishing are
hypotheses.  It does not prove that an unrestricted Erdős #243 orbit enters
this regime; integer centered errors with cofinally unbounded negative
excursions remain outside the theorem.  Erdős #243 therefore remains open.

`Challenge.lean` imports only Mathlib and exposes the complete two-conclusion
endpoint.  `Solution.lean` transports the source-current zero-defect theorem
and its paper-facing Sylvester consequence.  The deliberate negative keeps
only the recurrence conclusion, so Comparator must reject it as an incomplete
statement rather than accepting a watered-down version of the result.

## Verification

From `formal_math/erdos257_period_noncollapse`:

```sh
./scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification243BoundedNegativePartRigidity/Challenge.lean \
  ExternalVerification243BoundedNegativePartRigidity/Solution.lean \
  ExternalVerification243BoundedNegativePartRigidity/NegativeSolution.lean \
  ExternalVerification243BoundedNegativePartRigidity/AxiomAudit.lean
```

The checked-in replay actuator runs the positive and deliberate-negative
Comparator configurations on a supported Linux host.  Exit `75` is an
environment-unavailability receipt, not a Comparator verdict.

## Palomar disposition

This is a first-wave Palomar candidate.  Eventual exact rigidity of an entire
signed-error regime, without any periodicity hypothesis, is a coherent
research-note result with a number-theory and formal-mathematics audience.
The open unrestricted parent problem is the claim boundary, not a reason to
withhold this theorem.

Submission still requires a public GitHub repository at a full immutable
commit SHA, this exact config path, terminal positive acceptance, deliberate
negative rejection, and source-current metadata.  These local files are not a
Palomar decision, registry entry, novelty ruling, or peer review.
