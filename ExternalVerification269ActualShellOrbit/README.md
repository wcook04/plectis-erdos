# Erdős #269: the actual infinite dyadic shell orbit

This package isolates the source-specific infinite orbit, rather than a
generic bounded-radix lemma or a conditional carry interface. For the literal
`{2,3,5}`-smooth mass in each half-open dyadic shell, the compared theorem
asserts simultaneously that

- the shell-mass sequence is summable;
- its genuine infinite `tsum` tail obeys the exact ordered affine recurrence
  at every scale; and
- either some normalized tail state is an integer, or cofinally many states
  lie at distance at least `1/31` from every integer.

The definitions retain the actual smooth exponent boxes, running-height
weights, internal odd-prime thresholds, exact radix alphabet, ordered digit,
infinite tail, and height normalization.

## Mathematical boundary

The theorem constructs and controls the actual #269 shell orbit with no
abstract tail or digit input left. Its dichotomy is exact, but it does not
exclude the integral-state branch. It therefore does not prove irrationality
or transcendence of the three-prime running-LCM series. It also does not
assert eventual separation, positive density of separated scales, or a
distance larger than `1/31`.

`Challenge.lean` imports only Mathlib. `Solution.lean` transports
`summable_dyadicShellMassR235`,
`dyadicNormalizedShellTsumTailR235_succ`, and
`dyadicShellTsumTail_integer_or_cofinal_far` from
`ErdosProblems/Erdos269/DyadicShellSummability.lean` into one coherent
declaration.

## Comparator and validation

`comparator.json` selects the single composite theorem with NanoDa enabled
and exactly the standard Palomar axiom budget. The negative configuration
uses a same-named theorem with an extra `True` hypothesis, which Comparator
must reject as a declaration-type mismatch.

Focused Challenge, Solution, deliberate-negative, and AxiomAudit module
builds pass, and the compared theorem reports exactly Palomar's permitted
axiom budget. Supported terminal Comparator/NanoDa replay remains pending;
the presence of these files is not itself a Comparator receipt.

## Palomar disposition

This is a coherent candidate because it upgrades the generic escape mechanism
to the literal convergent source tail and preserves the exact remaining
branch. Submission still requires a public repository at a pinned full commit
SHA, terminal positive acceptance, and deliberate-negative rejection. Nothing
here is a Palomar decision, registry entry, novelty ruling, or peer review.
