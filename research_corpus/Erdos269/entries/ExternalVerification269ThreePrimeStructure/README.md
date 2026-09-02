# Erdős #269: exact three-prime running-LCM structure

This package isolates seven unconditional structural results for the first open
three-prime smooth case.  For pairwise-distinct primes `p,q,r` and `x ≠ 0`,
the literal LCM of every `{p,q,r}`-smooth number at most `x` is exactly

\[
p^{\lfloor\log_p x\rfloor}
q^{\lfloor\log_q x\rfloor}
r^{\lfloor\log_r x\rfloor}.
\]

This is an identity, not an upper bound or an asymptotic.  More strongly, for
every order `n` the package produces injective row and column families whose
`n × n` running-LCM kernel determinant is nonzero simultaneously in every
remaining layer.  Consequently there is no finite exact representation
`∑ l, f l i * G l j k`.  The smallest `{2,3,5}` rectangle is retained as a
concrete instance: its determinant is exactly `-1/15`.

The Comparator surface also carries the exact intermediate geometry used by
the paper rather than hiding it behind the rank endpoint.  The kernel is
constant on each three-prime logarithmic cell; the first `count` positive
jumps in each channel form exactly `3 * count` distinct values; every finite
kernel box groups exactly by genuine running-LCM height with fibre
cardinalities as coefficients; and every multiplicative-width shell satisfies
the denominator-free quadratic multiplicity bound
`9 * card ≤ (j + 3)^2` under the stated sorted-height hypotheses.

The deliberate negative retains the LCM identity, weakens the exact minor
value to mere nonvanishing, and omits the arbitrary-order theorem.  Comparator
must reject both losses of information.

## Mathematical boundary and Palomar disposition

These theorems give the exact finite LCM coordinate and prove an
arbitrary-order, infinite-rank non-separability obstruction.  They do not prove irrationality or
transcendence of the three-prime running-LCM series, and Erdős #269 remains
open.  The stronger two-prime transcendence argument in the governing paper
uses an external analytic theorem and is not represented here as Lean-checked.

This is a Palomar candidate as the structural core of a serious #269 note.
Submission still requires a public immutable commit, terminal positive and
deliberate-negative Comparator receipts, current metadata, and operator
authorization.  This local package is not a Palomar verdict, novelty ruling,
or peer review.
