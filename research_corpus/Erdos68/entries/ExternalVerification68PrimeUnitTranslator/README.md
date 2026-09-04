# Erdős #68: prime-unit translator and remote channel reduction

This package isolates a genuinely different #68 mechanism from the carry
families.  For every prime `p`, the coefficient pair `(p, -1)` on indices
`(p - 1, p)` has zero factorial moment, vanishes in every channel except `p`,
and contributes exactly one to the normalised residual.  It is therefore an
exact integer translation direction, not an approximate correction.

The principal theorem uses that direction after an explicit factorial-grid
Cramer construction.  For every channel rank and support threshold it produces
a finite integer vector entirely beyond the threshold, kills all channels from
`2` through the requested cutoff, keeps nonzero factorial moment, and moves the
residual into the closed interval of radius `1/2`.

## Exact boundary

The result is unconditional, but the bound is non-strict: the reduced residual
may equal zero.  The source has a strict version only under the additional
assumption that the un-translated residual is not an integer.  This package
deliberately excludes that conditional theorem because no producer proves its
extra assumption for the Cramer vectors.  Nothing here proves irrationality of
the factorial-gap series.

`Challenge.lean` imports only Mathlib.  `Solution.lean` transports the exact
profile, integer-translation law, and remote reduction from
`ErdosProblems.Erdos68.PrimeUnitTranslator`.  The negative configuration binds
a same-named theorem with an extra `True` hypothesis and must be rejected as a
declaration-type mismatch.

## Palomar disposition

This is a first-wave candidate family: it has a compact Mathlib-only statement,
an unconditional principal endpoint, an exact source transport, the standard
three-axiom budget, and NanoDa enabled.  No Comparator or Palomar run, external
review, novelty ruling, or submission is claimed by these files.
