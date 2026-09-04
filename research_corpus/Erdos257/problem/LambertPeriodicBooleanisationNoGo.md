# An eventual-periodicity obstruction to Lambert Booleanisation

Put
\[
 w_d=\frac1{2^d-1}
\]
and let (B\subseteq\mathbb N_{>0}) be a Boolean support.  Its Lambert
coefficient sequence is
\[
 a_B(n)=\#\{d\in B:d\mid n\}.
\]
Absolute convergence gives the standard change of coordinates
\[
 \sum_{d\in B}w_d=\sum_{n\geq1}\frac{a_B(n)}{2^n},                 \tag{1}
\]
and Möbius inversion recovers the support indicator:
\[
 {f1}_B=a_B*\mu.                                                \tag{2}
\]
This note records an exact obstruction to obtaining a rational value by
making the multiplicity sequence in (1) eventually periodic.

## The theorem

> **Eventual-periodicity theorem.**  Suppose (T\geq1) and there is an
> (N\) such that
> \[
>  a_B(n+T)=a_B(n)\qquad(n\geq N).                               \tag{3}
> \]
> Then every element of (B) divides (T).  In particular, (B) is
> finite.  Conversely, if every element of (B) divides (T), then
> (a_B) is (T)-periodic from the first term.

To prove the forward direction, take (d\in B) and suppose that
(d\nmid T).  Since (d>0), the integer
\[
 k=dN+1,qquad n=kT
\]
satisfies (n\geq N), and (d\nmid n): reduction modulo (d) gives
(n\equiv T\pmod d).  Iterating (3) along the residue-zero class modulo
(T) gives
\[
 a_B(dn)=a_B(n).                                                  \tag{4}
\]
Every divisor of (n) is a divisor of (dn).  Hence every selected divisor
counted by (a_B(n)) is also counted by (a_B(dn)).  The selected divisor
(d) is counted on the right but not on the left, so
\[
 a_B(dn)\geq a_B(n)+1,
\]
contradicting (4).  Thus (d\mid T).

For the converse, if (d\mid T), then (d\mid n) if and only if
(d\mid n+T).  The selected-divisor sets at (n) and (n+T) are therefore
identical.

## Consequence for the signed and product identities

The signed identity
\[
 \sum_{d\geq1}\frac{\mu(d)}{2^d-1}=\frac12
\]
and the product-anchor identity
\[
 \frac1{465}=w_4w_5
 =\sum_{d\geq1}c_{4,5}(d)w_d
\]
both provide rational Lambert identities before Booleanisation.  In the
second formula, (c_{4,5}(d)) counts primitive positive solutions of
(4p+5q=d).  Any recut which produces a Boolean support (B) can be read,
via (1)--(2), as replacing the signed or multiple coefficients by the
selected-divisor sequence (a_B).

The theorem shows that (a_B) cannot become periodic after any finite
stage unless the support is finite.  Thus a direct construction of an
infinite rational Boolean subsum cannot close by a periodic multiplicity
output or by a paired-sign recut whose resulting selected-divisor sequence
is eventually periodic.  A successful construction must retain genuinely
aperiodic divisor-count state.

This is not an irrationality theorem.  A rational value of the binary sum
on the right of (1) does not force the integer sequence (a_B(n)) itself to
be eventually periodic, because coefficients larger than one admit carries.
The theorem excludes the periodic-coefficient route, not every aperiodic
global Booleanisation of the Möbius or primitive-lattice identities.

## Exact audit

The companion script checks the divisor-inclusion witness used in the proof
and exhausts small periodic coefficient words.  Every Boolean Möbius inverse
which survives the audit is supported on divisors of the proposed period.

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/lambert_periodic_booleanisation_no_go.py
```
