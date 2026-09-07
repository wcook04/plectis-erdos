# Zudilin all-`d` first-block resultant proof

## Theorem

Fix `d>=1` and a primitive `d`-th root `zeta`.  Let

`a_s=S_(d+s)^(d)`, `0<=s<d`,

be the first block of leading `Phi_d` source residues from
`ZudilinSingleChannelBlockFormulaProof.md`, and let

`K_d=12 d^3 M_d(zeta)^3`,

where `M_d=(p^d-1)/Phi_d`.  The normalized first cross block is the wrapped
Hankel matrix

`H_(i,j)=a_(i+j)` if `i+j<d`,

`H_(i,j)=K_d a_(i+j-d)` if `i+j>=d`,

for `0<=i,j<d`, up to invertible diagonal row and column factors.

Then `det(H) != 0` for every `d`.  More precisely, after division by the
nonzero scalar `a_0`, the anti-diagonal is the unique determinant term of
lowest valuation at a prime above `2`.

Together with the all-`d` source block law and fixed border ratios, this proves
that Zudilin's complete cyclotomic first-appearance associated-graded residue
is nonzero for every `d`.  It eliminates the expanding homogeneous boundary
mode.  It does not yet prove that the cumulative extracted degree reaches the
irrationality threshold at `p=3/2`.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction and analytic
`q`-order estimate are due to Wadim Zudilin, *On the irrationality of
generalized q-logarithm*, Research in Number Theory 2 (2016), Article 15,
DOI [10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).
The downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state this wrapped first-block resultant or the all-`d` first-appearance
noncancellation.  Those arguments and their finite executable certificates are
authored in this repository.

## 1. Exact first-block symbol

Write `w_s=a_s/a_0`.  The leading single-channel formula at quotient block
`q=1` gives

`w_s=(-1)^s zeta^s Q_s(zeta)^3 F_s(zeta)`,

where

`Q_s(p)=product_(b=1)^s (p^b-1)`

and

`F_s(p)=sum_(b=0)^s (-1)^b p^(b(b+1)/2)
  [s choose b]_p [s+b choose b]_p`.

This is also valid when a displayed finite sum vanishes; no quotient by
`F_s` is used.  Every `F_s(zeta)` is a cyclotomic integer.

At `s=d-1`, every summand with `b>=1` contains a numerator factor
`p^d-1` and no denominator factor vanishing at `zeta`.  Hence

`F_(d-1)(zeta)=1`.

Also

`Q_(d-1)(zeta)=(-1)^(d-1)d`.

The signs cancel, so the terminal symbol has the especially simple value

`w_(d-1)=d^3 zeta^(-1) != 0`.

The base coefficient itself is nonzero.  The formula from the preceding
single-channel proof gives

`C_d^(d)=zeta A_d^3 M_d(zeta)^2 (-1)^(d-1)`,

with `A_d=(-1)^(d-1)d`; and `S_d^(d)=-3C_d^(d)` by the proved all-index
channel identity.  Thus normalizing by `a_0` loses no information.

## 2. Wrapped Hankel resultant

Put

`W_d(x)=sum_(s=0)^(d-1) w_s x^s`.

The normalized matrix has entries `w_(i+j)` before the wrap and
`K_d w_(i+j-d)` after it.  Direct diagonalization on the roots of
`K_d x^d-1` gives

`det(H/a_0)
 =(-1)^((d-1)(d-2)/2) Res_x(W_d(x), K_d x^d-1)`.

Indeed, for any root `t` of `K_d t^d=1`, the vector
`(1,t,...,t^(d-1))^T` is sent to `W_d(t)` times the corresponding vector at
`t^(-1)`.  Taking the two Vandermonde determinants supplies the displayed
sign and the factor `K_d^(d-1)` already present in the resultant convention.

This identity exposes singularity as a common-root question.  The valuation
argument below decides it without locating or estimating those roots.

## 3. Cyclotomic `2`-adic weights

First suppose `d` is even.  Write

`d=2^a m`, `a>=1`, `m` odd, and `e=2^(a-1)`.

Choose a prime above `2` in `Q(zeta)` and normalize its valuation `v` by

`v(zeta^m-1)=1`.

The odd-order part is unramified and the `2^a`-part is totally ramified, so

`v(2)=e`,

and, for `1<=b<d`,

`v(zeta^b-1)=0` if `m` does not divide `b`,

`v(zeta^(mc)-1)=2^v_2(c)` for `1<=c<2^a`.

Define

`h(u)=sum_(c=1)^u 2^v_2(c)`, `h(0)=0`,

and the first-block lower weights

`q_s=3 h(floor(s/m))`.

Because `F_s(zeta)` is integral, the exact symbol formula gives

`v(w_s)>=q_s`.

For the terminal entry equality holds:

`q_(d-1)=3 h(2^a-1)=3ae=v(d^3 zeta^(-1))`.

The identity `h(2^a-1)=ae` follows by grouping the integers according to
their exact `2`-adic order: each of the `a` groups contributes `e`.

The wrap multiplier has exact valuation

`v(K_d)=(3a+5)e`.

To see this, the local cyclotomic different gives

`v(Phi_d'(zeta))=(a-1)e`.

Since `M_d(zeta)=d zeta^(-1)/Phi_d'(zeta)`, it follows that `v(M_d)=e`.
The three parts of `12d^3M_d^3` then contribute `2e`, `3ae`, and `3e`.

For later use, the elementary dyadic average satisfies

`h(u)<=((a+1)/2)u`, `0<=u<2^a`.

Indeed,

`h(u)=u+sum_(r=1)^(a-1) 2^(r-1) floor(u/2^r)`,

and replacing every floor by its argument proves the bound.  Equality is
attained at `u=2^(a-1)`.

## 4. One affine line isolates the anti-diagonal

Let `q*=q_(d-1)=3ae` and choose the rational slope

`c=(3a+4)/(2m)`.

Consider the line in the raw Hankel index `t=i+j`:

`ell(t)=q*+c(t-d+1)`.

For an unwrapped index `s<d-1`, put

`u=2^a-floor(s/m)-1`.

Then `d-1-s>=mu` and `q*-q_s=3h(u)`.  Therefore

`(q*-q_s)/(d-1-s)
 <=3h(u)/(mu)
 <=3(a+1)/(2m)
 <c`.

Thus `q_s>ell(s)`.

For a wrapped residue `0<=r<d-1`, use the same

`u=2^a-floor(r/m)-1`,

now possibly `u=0`.  Since `r+1<=m(2^a-u)`, it is enough to prove

`v(K_d)+q_r>c m(2^a-u)`.

Twice the difference between the two sides is

`2^a+(3a+4)u-6h(u)`.

The dyadic average bound makes this at least `2^a+u`, hence it is strictly
positive.  Every wrapped entry is also strictly above `ell`.

If `d` is odd, reduction at a prime above `2` preserves the order `d` of
`zeta`.  All `Q_s(zeta)` with `s<d` are units, while `v(K_d)>=v(4)>0` and
`w_(d-1)=d^3zeta^(-1)` is a unit.  The simpler slope `c=1/d` gives the same
strict separation.

Now let `sigma` be any determinant permutation.  The affine weights sum to

`sum_i ell(i+sigma(i))=d q*`,

because `sum_i i=sum_i sigma(i)=d(d-1)/2`.  Equality with the true entry
valuations occurs on the anti-diagonal `sigma(i)=d-1-i`.  Every other
permutation uses at least one strictly separated edge.  Consequently the
anti-diagonal is the unique lowest-valuation determinant term, with value

`(-1)^(d(d-1)/2) w_(d-1)^d`.

It cannot cancel.  In particular,

`v(det(H/a_0))=3aed` for even `d`,

and `v(det(H/a_0))=0` for odd `d`.

This proves `det(H)!=0` for every cyclotomic index.

## 5. First-appearance consequence

The cross matrix `X` in `ZudilinFirstAppearanceBorderFormLab.md` has `d+1`
columns.  Its first `d` columns are `H` up to diagonal units, while the all-`d`
block formula makes the last column proportional to the first.  Nonsingularity
of `H` therefore gives full row rank and forces the maximal-minor/null vector
to have support only at its two endpoints.

The same all-`d` block formula supplies the corner ratios `11/4` and `50/3`.
The bordered identity consequently reduces the complete minimum layer to

`6(-1)^d Res_d=73 T_00`.

Here the endpoint cofactor is nonzero by `det(H)!=0`, and the top-left source
entry is nonzero by the explicit `a_0` formula and `K_d!=0`.  Hence
`Res_d!=0` for every `d`.

This is the desired one-way local result: no cyclotomic index can create an
expanding homogeneous boundary cancellation at first appearance.  Additional
first-appearance index audits are now mathematically redundant.

The remaining #1049 question in this construction is global rather than
local.  One must sum or norm the proved first-appearance factors strongly
enough to compare their cumulative degree with the rational-base height
threshold.  The existing scalar-plus-border ceiling proves that mere forced
entry valuations are insufficient; the new nonzero residues make an exact
resultant/norm growth computation the next discriminating target.

## Executable certificate

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_first_block_resultant.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_first_block_resultant_receipt.json
```

The checker validates the affine inequalities through `d=256`, independently
replays the minimum assignment through `d=14`, reconstructs the exact
cyclotomic symbol and terminal identity through `d=12`, and computes direct
resultants through `d=6`.  Those finite checks are regressions of the authored
all-`d` argument, not the source of its universal quantifier.
