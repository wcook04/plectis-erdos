# Erdős #1049: rational-base cleared-tail barrier

This package exposes one coherent negative mechanism at rational bases.  For
the cleared tail state

\[
Q_N=B r^N\left(F-\sum_{m<N}
  \frac{c(m+1)s^{m+1}}{r^{m+1}}\right),
\]

the exact recurrence is

\[
Q_{N+1}=rQ_N-Bc(N+1)s^{N+1}.
\]

When `s ≥ 2` and the integer data are positive, the forcing term is at least
`2^(N+1)`.  The same denominator-base tax makes the literal coordinatewise
Erdős corridor impossible at `3/2` whenever both the shift and cleared window
are nonempty.

## Exact boundary

The recurrence is an algebraic identity for an abstract coefficient stream.
It is not derived from rationality of the Lambert value.  The corridor theorem
excludes one six-condition clearing scheme; it does not exclude other
linear-form, Padé, adelic, or Mahler constructions and does not prove
irrationality at `3/2`.

`Challenge.lean` imports only Mathlib and restates the required definitions.
`Solution.lean` transports the three exact source declarations from
`ErdosProblems.Erdos1049.RationalBaseLambert`.  The negative configuration
changes the recurrence theorem type by adding an extra `True` hypothesis and
must be rejected.

The positive configuration permits exactly `propext`, `Quot.sound`, and
`Classical.choice`, and enables NanoDa.  Public pinning, supported Comparator
replay, deliberate-negative rejection, and Palomar review remain separate
mechanical steps.
