# Zudilin first-appearance bordered quadratic-form lab

## Structural question

At cyclotomic first appearance `N=2d+1`, the minimum residual order is one.
The support theorem counts `(d+1)2^d` minimum permutations, but that
exponential description does not reveal why their signed source residues
should be nonzero.

This lab asks whether the complete layer is controlled by a one-dimensional
boundary mode of the zero-weight cross blocks.

## Exact bordered identity

Split indices into `A={0,...,d-1}` and `P={d,...,2d}`.  Retain only

- the zero-weight `A -> P` block `X`, of shape `d x (d+1)`;
- the zero-weight `P -> A` block `Y`, of shape `(d+1) x d`; and
- the weight-one `P -> P` block `Z`.

An order-one permutation uses exactly one entry of `Z`, no `A -> A` entry,
and otherwise uses `X` and `Y`.  Therefore the minimum layer is the coefficient
of `t` in

`det([[0,X],[Y,tZ]])`.

Define maximal-minor vectors

`a_i=(-1)^i det(Y without row i)`,

`b_j=(-1)^j det(X without column j)`.

Cofactor expansion at the unique `Z` entry gives the exact all-matrix identity

`coefficient_t = (-1)^d a^T Z b`.

The same minors give `a^T Y=0` and `Xb=0`.  Thus `a` and `b` are boundary null
vectors, not bookkeeping devices for the original permutation sum.

## Zudilin specialization

The local primitive residue matrix is symmetric and Hankel up to diagonal unit
scaling.  Hence `Y=X^T`, `Z=Z^T`, and the two cofactor vectors agree.  The
entire first-appearance layer becomes

`(-1)^d v^T Z v`,

where `v` spans the one-dimensional nullspace of `X` whenever `X` has full row
rank.  This changes the analytic problem: uniform cyclotomic noncancellation is
now a boundary quadratic-form question, with recurrence, conjugate-norm, and
resultant routes available.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery reused by the local
residue matrices, is due to Wadim Zudilin, *On the irrationality of generalized
q-logarithm*, Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the boundary quadratic-form identity, endpoint cofactor support,
or the finite subset-DP residue contractions recorded here.  Those specialized
residue matrices, exact replays, and the all-index proof target are authored in
this repository.

The checker reconstructs the exact local residue matrices for `d=1,...,4`,
consumes the committed `Phi_5` primitive-row receipt for `d=5`, and verifies:

- both cross blocks and the border are symmetric transposes;
- the cofactor vectors are equal and satisfy both null relations; and
- `(-1)^d v^T Z v` exactly reproduces every committed subset-DP residue.

## Endpoint collapse

The exact cofactor vectors for `d=1,...,5` have the stronger form

`v=(v_0,0,...,0,v_d)`,

with both endpoints nonzero.  Therefore

`(-1)^d v^T Z v`

uses only the four corner entries `Z_(0,0), Z_(0,d), Z_(d,0), Z_(d,d)`.
The checker recomputes this two-by-two corner contraction and verifies that it
still equals the complete subset-DP residue at every tested index.

This is the first concrete candidate for an all-index proof.  Endpoint support
means the first and last columns of `X` are linearly dependent modulo the span
of its interior columns, while every interior-column deletion drops rank.  A
source recurrence proving that statement would replace the entire family of
exponential determinant sums by two endpoint cofactors and four explicit
border residues.  Noncancellation could then be attacked by a cyclotomic norm
or resultant of that corner form.

## Fixed `73` identity

Write the unsigned endpoint contraction as

`T_00 + T_cross + T_dd`,

where

- `T_00=v_0^2 Z_(0,0)`;
- `T_cross=v_0 v_d (Z_(0,d)+Z_(d,0))`; and
- `T_dd=v_d^2 Z_(d,d)`.

For every exact quotient `d=1,...,5`, the checker finds

`2 T_cross + 11 T_00 = 0`,

`3 T_dd - 50 T_00 = 0`.

Consequently

`6 (-1)^d Res_d = 73 T_00`.

This explains the common prime factor `73` in all five previously computed
residues; it was not a numerical coincidence.  It also removes the remaining
quadratic-form ambiguity.  If the endpoint support and these two ratios hold
for every `d`, uniform first-appearance noncancellation follows as soon as the
top-left cofactor and border entry are nonzero.  Those are triangular/local
source statements, rather than exponential determinant statements.

This is a structural reduction and exact `d<=5` endpoint/ratio law, not yet a
proof that the identities hold for every `d`.  Further cyclotomic indices are
not progress unless they test the specific cross-column recurrence or fixed
corner ratios above.

## Reproduction

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_first_appearance_border_form.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_first_appearance_border_form_receipt.json
```
