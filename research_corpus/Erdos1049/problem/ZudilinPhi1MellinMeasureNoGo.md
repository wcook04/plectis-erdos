# Zudilin `Phi_1` canonical Mellin-measure no-go

## Mechanism eliminated

The all-rank `Phi_1` kernel is controlled by

`m_n=(n!)^3 H_n`.

A natural attempt to prove the needed southeast Hankel matrix positive
definite is to realize the shifted sequence `m_(n+2)` as moments of a positive
measure.  The source-natural Mellin representation does **not** do this: its
density changes sign on an explicit interval.

Let `X_1,X_2,X_3` be independent unit exponential random variables and let
`T=X_1 X_2 X_3`.  Its density `f_3(t)` is strictly positive for `t>0` and has
Mellin transform

`int_0^infinity t^(s-1) f_3(t) dt = Gamma(s)^3`.

Differentiate in `s`.  Since

`Gamma'(s)=Gamma(s) psi(s)`,

the signed density

`w(t)=f_3(t)(gamma+(1/3)log t)`

has moments

`int_0^infinity t^n w(t) dt
 = Gamma(n+1)^3(psi(n+1)+gamma)
 = (n!)^3 H_n
 = m_n`.

The factor `gamma+(1/3)log t` is negative for
`0<t<exp(-3gamma)`, zero at `exp(-3gamma)`, and positive above that point.
Multiplying by `t^2` to represent the shifted sequence `m_(n+2)` does not
change its sign.  Therefore neither the canonical product-exponential density
nor its shifted density is a positive Gram measure.

This is a one-way no-go for the most immediate positivity proof suggested by
the factorial cube.  It does not show that the shifted Hankel matrix fails to
be positive definite: a different positive representing measure, or a direct
condensation/sign-regularity proof, could still exist.  It also says nothing
about the `Phi_2` or higher-cyclotomic layers.

## Why the sign change matters

The bordered identity in `ZudilinPhi1AssociatedGradedKernel.md` reduces
all-rank noncancellation to the southeast matrix

`((i+j)!)^3 H_(i+j), 1<=i,j<N`.

If the canonical Mellin density were positive, this matrix would be a strict
Gram matrix immediately: a nonzero polynomial with no constant term would
have a positive squared integral.  The explicit negative interval prevents
that argument.  Numerical positivity of more leading minors cannot repair the
failed measure; the next route must actually construct an alternate positive
functional or prove determinant signs by recurrence, total positivity, or
condensation.

## Source and attribution boundary

The surrounding Hankel mechanism is grounded in Wadim Zudilin, *On the
irrationality of generalized q-logarithm*, Research in Number Theory 2 (2016),
Article 15, DOI `10.1007/s40993-016-0042-x`. The downloaded primary source is
retained at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`: source
TeX lines 278–302 define the Hankel determinants and their leading q-order,
lines 310–350 prove the backward-shift lemma, and lines 362–377 derive the
determinant order bound. Those passages motivate the factorial-harmonic Hankel
consumer but do **not** state the product-exponential Mellin representation or
its sign change.

The differentiated \(\Gamma(s)^3\) identity, the density
\(f_3(t)(\gamma+\log(t)/3)\), and the threshold \(\exp(-3\gamma)\) are
repository-authored elementary analysis. The exact checker records integer
moment regressions and the two sign witnesses; it eliminates only this
canonical product-exponential positive-measure route. It does not rule out an
alternate representing measure, prove Hankel positive-definiteness or failure,
or establish irrationality of Erdős #1049.

The zeroth moment supplies a useful consistency check.  Because `H_0=0`, the
signed density has total mass zero:

`psi(1)+gamma=0`.

It is nevertheless nonzero and has positive higher moments.  This makes the
sign change unavoidable, rather than an artefact of an imprecise density
formula.

## Executable identity check

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_phi1_mellin_measure.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_phi1_mellin_measure_receipt.json
```

The checker verifies the differentiated Gamma identity at exact integer
arguments and records the exact signs on the two sides of the threshold.  The
all-rank result is the Mellin differentiation above, not an extrapolation from
the regression range.  Erdős #1049 remains open.
