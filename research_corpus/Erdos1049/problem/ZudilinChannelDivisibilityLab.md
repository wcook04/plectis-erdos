# Zudilin channel-divisibility lab

## Global target exposed by block collapse

Put

`P_n(p)=product_(1<=j<=n)(p^j-1)`.

The complete local block-collapse computation found that the leading
inhomogeneous source residues satisfy `B=2C` for every tested cyclotomic index
and residue class.  Those separate local identities are all consequences of
one stronger polynomial statement:

`p^(n+1) P_n(p)^3 divides Btilde_n(p)-2 Ctilde_n(p)`.

Indeed, the scalar row content is `H_n=P_n^3/L_n`, where

`L_n=product_(1<=d<=n) Phi_d`.

The displayed divisor gives each `Phi_d`, `d<=n`, order
`3 floor(n/d)`, exactly one above the forced scalar order
`3 floor(n/d)-1`.  Therefore it makes the leading `B` and `2C` residues equal
simultaneously at every such cyclotomic index.  This replaces an expanding
family of root-of-unity statements with one all-`n` polynomiality theorem.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery, is due to Wadim
Zudilin, *On the irrationality of generalized q-logarithm*, Research in Number
Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the polynomial divisor `p^(n+1) P_n^3`, the `B-2C` cancellation,
or the specialized quotient signatures above.  Those source-specific claims,
finite checks, and the all-`n` proof target are authored in this repository.

## Exact result

For every `1<=n<=7`, exact division in `Z[p]` gives

`Btilde_n-2 Ctilde_n = p^(n+1) P_n^3 D_n(p)`

with zero remainder.  The quotient has the uniform signatures

`deg D_n=(n+1)(3n-2)/2`,

`ord_p D_n=1`,

`D_n(1)=n^3`.

Moreover `gcd(D_n,P_n)=1` at every tested row.  Thus the gained order is
exactly one for every `Phi_d` in `P_n`, not an artifact of a still larger
unseen cyclotomic divisor.  The computation reaches a degree-168 source
difference and a degree-76 normalized quotient at `n=7`.

This is not an all-`n` proof.  It is a one-way structural opening: the
previously observed channel equality has a single global algebraic source,
and the exact quotient signatures constrain the certificate rather than
licensing further row extension.

## Why this is a polynomiality problem

At `x=z=1`, Zudilin's primary-source clearing factor is

`Dclear_n=p^(-3n(n+1)/2) P_n^3`.

The source formulas have

`Btilde_n=Dclear_n B_n`, `Ctilde_n=Dclear_n C_n`,

up to the common source power already incorporated by the executable
constructor.  Consequently the full `P_n^3` divisor is equivalent to the
rational source combination `B_n-2C_n` losing all denominators
`p^ell-1`, `1<=ell<=n`.  A proof should not factor a growing polynomial.  It
should prove cancellation of those poles in the two finite sums.

The primary paper notes that the hypergeometric remainder has a hidden
`x,z` symmetry supplied by Heine's transformation.  That symmetry is the
first analytic route: specialize its two parameter channels at `x=z=1` and
identify the resulting derivative or divided-difference relation whose
inhomogeneous part is `B_n-2C_n`.

There is a complementary source-sum route.  For each denominator
`p^ell-1`, split the `B` sum at its harmonic index and reverse the triangular
`C` sum.  A finite `q`-binomial telescope should pair their residues with
coefficient `2`.  The certificate must leave a polynomial remainder `D_n`
whose endpoint value is `n^3`; this endpoint condition rules out a vacuous
zero certificate and ties the global identity back to the committed
factorial-harmonic `Phi_1` kernel.

## Consequence for the boundary mode

An all-`n` proof of the displayed divisor eliminates cross-channel
cancellation from the first-appearance problem for every `d` at once:

`-B_n-C_n = -3 C_n` on the leading `Phi_d` layer.

The remaining block-collapse theorem then needs only the `C` sum.  Applying
`q`-Lucas to its already isolated residue window must produce the universal
quotient constants

`1`, `11/4`, `50/3`.

Those constants feed the proved two-endpoint boundary contraction, whose
nonzero factor is `73`.  Thus the global channel divisor is a concrete
analytic precursor to killing the expanding homogeneous boundary mode; it
does not itself establish the remaining quotient-block identity, the full
denominator charge, or irrationality.

## Reproduction

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_channel_divisibility.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_channel_divisibility_receipt.json
```

The checker supports independent row slices with `--row-index`,
`--result-output`, and `--result-only`, followed by exact combination through
repeated `--from-result`.  Its canonical receipt binds the primary-source
extract, exact polynomial constructor, this analytic target, previous
block-collapse result, and Lean consumer by content hash.
