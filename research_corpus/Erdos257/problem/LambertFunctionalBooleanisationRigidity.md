# Functional rigidity of Lambert Booleanisation

Let

\[
  L_c(r)=\sum_{d\ge 1}c(d)\frac{r^d}{1-r^d}
\]

be the Lambert series of an integer arithmetic weight `c`.  A global
Booleanisation would replace `c` by a weight `b(d)\in\{0,1\}` while preserving
this Lambert series as a formal power series, or equivalently as an analytic
function throughout a neighbourhood of the origin.

That is impossible for the Möbius, totient, and primitive-conductor rational
identities.  The obstruction is exact and has nothing to do with periodicity
or with a choice of carry.

## Rigidity theorem

> **Theorem.**  Convolution by the constant-one arithmetic function `ζ` is
> injective on integer arithmetic functions.  Consequently, if
> \[
>   L_c(r)=L_b(r)
> \]
> as formal power series and `b` is Boolean on the positive integers, then
> `c=b`; in particular, `c` was already Boolean.

Indeed, the coefficient of `r^n` in `L_c` is

\[
  (c*\zeta)(n)=\sum_{d\mid n}c(d).
\]

Equality of the formal Lambert series therefore gives

\[
  c*\zeta=b*\zeta.
\]

Convolving with the Möbius function and using
`μ*ζ=1` gives `c=b`.  The same conclusion follows from equality as analytic
functions on any interval accumulating at zero, by uniqueness of power-series
coefficients.  No boundedness, periodicity, or finite-support hypothesis is
used in the formal argument.

Lean checks the injectivity statement as
`mul_zeta_injective` in
[`LambertFunctionalRigidity.lean`](../../Erdos257PeriodNoncollapse/LambertFunctionalRigidity.lean).

## Exact exclusions of the landed rational rungs

The same module proves three coefficientwise no-go theorems.

1. The Möbius weight is not Boolean because `μ(2)=-1`.  Hence no Boolean
   weight has the same formal Lambert series as `μ`, even though
   \[
     L_\mu(1/2)=\sum_{d\ge1}\frac{\mu(d)}{2^d-1}=\frac12.
   \]
2. The totient weight is not Boolean because `φ(3)=2`.  Hence no Boolean
   weight globally preserves the identity
   \[
     L_\varphi(r)=\frac{r}{(1-r)^2},
   \]
   including its rational value `L_φ(1/2)=2`.
3. For the primitive-conductor weight `A=φ*μ`, one has `A(5)=5-2=3`.
   It likewise has no coefficientwise Boolean Lambert normalisation.

The checked declarations are
`no_boolean_formal_lambert_moebius`,
`no_boolean_formal_lambert_totient`, and
`no_boolean_formal_lambert_primWeight`.  Their axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`.

## What changes after this obstruction

There are two different problems which should no longer be conflated:

* A **global Lambert Booleanisation** preserves `L_c(r)` as a series or
  function.  The theorem rules this out unless the source coefficient was
  already Boolean.
* A **single-point dyadic recut** asks only for
  \[
    L_b(1/2)=L_c(1/2).
  \]
  This scalar equality does not imply equality of any other Lambert
  coefficient or value.

Thus the rational Möbius identity supplies the target `1/2`, but not a global
normalisation mechanism.  Any successful aperiodic construction must be
specific to the point `r=1/2`; it must use the binary carrying interaction
between different power-series coefficients and therefore ceases to preserve
the Lambert identity it started from.

This is a no-go for the proposed global object, not an irrationality theorem
for every infinite Boolean Mersenne support.  The remaining single-point
problem is exactly the live Erdős #257 achievement-set question.

## Validation

```text
cd formal_math/erdos257_period_noncollapse
lake env lean Erdos257PeriodNoncollapse/LambertFunctionalRigidity.lean
```
