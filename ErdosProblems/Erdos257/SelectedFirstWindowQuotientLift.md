# Selected first-window quotient lift

## Result

For a fixed finite support `D` with all ranks at least two, Lean proves the
exact aggregate transition

\[
 Q_D(n+J)=2^JQ_D(n)+W_D(n,J),
\]

where

\[
 Q_D(M)=\sum_{d\in D}\left\lfloor\frac{2^M}{2^d-1}\right\rfloor
\]

and `W_D(n,J)` is the integer numerator of the frozen divisor-coefficient
window between rows `n` and `n+J`.  Equivalently,

\[
 W_D(n,J)=Q_D(n+J)-2^JQ_D(n).
\]

This is an all-window identity, obtained by iterating the already checked
one-row quotient transition.  It does not use the half-greedy orbit.

For the actual prefix

\[
 P_n=A_{1/2}\cap[2,n-1],
\]

the full-shell seam sum is also exactly a quotient row:

\[
 \operatorname{stemTruncatedSum}(n,P_n)=Q_{P_n}(2n).
\]

Consequently the checked full-shell identity becomes

\[
 \operatorname{greedyHalfFrozenMargin}(n-1,n)
   =Q_{P_n}(2n)-\bigl(2^{2n-1}-2^n\bigr).
\]

Thus

\[
 0\le \operatorname{greedyHalfFrozenMargin}(n-1,n)
 \quad\Longleftrightarrow\quad
 2^{2n-1}-2^n\le Q_{P_n}(2n).
\]

The focused build and serialized authority check passed for these statements.

## Stronger all-horizon cancellation

The finite-support centered carry at row `n-1` is the endpoint quotient
defect

\[
 C_{P_n}(n-1)=\bigl(2^{n-1}-1\bigr)-Q_{P_n}(n).
\]

Substitution into the quotient lift cancels the old quotient exactly.  The
resulting reusable identity is

\[
 \operatorname{greedyHalfFrozenMargin}(n-1,J)
 =Q_{P_n}(n+J)-2^J\bigl(2^{n-1}-1\bigr),
\]

and hence

\[
 0\le\operatorname{greedyHalfFrozenMargin}(n-1,J)
 \quad\Longleftrightarrow\quad
 2^J\bigl(2^{n-1}-1\bigr)\le Q_{P_n}(n+J).
\]

These two corollaries pass the focused build and serialized Lake authority
check.  Their axiom reports contain only the standard `propext`,
`Classical.choice`, and `Quot.sound` dependencies, with no `sorryAx`.

## Frontier effect

This is a coordinate theorem, not a proof of the open producer.  It shows
that the selected first-window charge, frozen-margin first passage, and the
moving quotient-row crossing are exactly the same boundary.  In particular,
the full-shell charge is not an independent producer.

The useful redirect is the all-horizon form.  The logarithmic first-passage
producer can now be attacked as the finite statement that, after an actual
skip at rank `n`, some

\[
 J\le 2(\lfloor\log_2 n\rfloor+1)
\]

satisfies

\[
 Q_{P_n}(n+J)\ge 2^J(2^{n-1}-1).
\]

This removes the rational remainder denominator and the real tail from that
subproblem entirely.  Any next computation in this lane should measure the
first quotient-crossing time and the individual divisor contributions to its
last deficient row; it should not expand the old finite survival horizon or
rederive another margin/budget alias.

## Source

- `SelectedFirstWindowQuotientLift.lean`
- checked prerequisites:
  `localPrefixQuotient_succ`,
  `mobiusCenteredHalfCarry_coe_finset_eq_localEndpointDefect`,
  `localMersenneQuotient_two_mul_eq_truncatedMersenneWeight`, and
  `greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target`
