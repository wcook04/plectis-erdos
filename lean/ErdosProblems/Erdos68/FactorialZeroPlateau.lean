import ErdosProblems.Erdos68.FactorialGapPlateauCore
import ErdosProblems.Erdos68.FactorialZeroPlateauCertificates
import ErdosProblems.Erdos68.FactorialZeroPlateauSupplement

/-!
# Erdős #68: factorial-grid plateaux and the exact carry criterion

Let `S` be the factorial-gap series and let `H_n` be its rational prefix
through index `n`.  The integer

`strictFacTop H_n n = floor(n! H_n) + 1`

is the first point of the `1 / n!` grid above `H_n`.  The first part of this
file proves that a rational value `S = a / q` forces this grid point to equal
the cleared numerator `(n! / q) a` once `n!` clears `q`.  In particular,
rationality forces explicit prime-power divisibility at suitable indices.

The second part compares consecutive grid points.  Their exact recurrence
has an integer carry `factorialGapStepCarry m`; rationality forces this carry
to be one eventually, and eventual unit carries conversely make the
normalized grid points stationary.  Thus the series is irrational exactly
when non-unit carries occur cofinally.  Exact computations at indices
`51`, `60`, and `67` give finite denominator lower bounds, but not the
required cofinal family.

The remaining theorems reformulate individual divisibility hits, doubled
prime square hits, and rational first crossings.  They also record two
generic coboundary lemmas and an independent factorial interval inequality.

The central open point is explicit: this file does not prove cofinally many
non-unit carries or strict-successor divisibility failures.  Consequently it
does not prove the irrationality of the factorial-gap series and does not
solve Erdős #68.
-/

/-! Compatibility import for the complete plateau family. Declarations are
owned by the core, finite-certificate and supplement modules above. -/
