# Zudilin rank-nine `Phi_4` associated-graded lab

## Mechanism question

`Phi_4=p^2+1` first has a positive forced residual-border order at rank nine.
The exact question is whether all determinant assignments of minimum total
`Phi_4` valuation cancel in `Q[mu,p]/(p^2+1)`, creating an extra cyclotomic
factor not visible entrywise.

This is a new cyclotomic quotient at its first possible rank.  It is not a
higher-rank replay of the `Phi_3` calculation.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery reused by the local
constructor, is due to Wadim Zudilin, *On the irrationality of generalized
q-logarithm*, Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the `Phi_4` rank-nine minimum-layer count, the residue
`-1655261568`, or the coefficientwise noncancellation result recorded here.
Those associated-graded reductions, finite replays, and their exact receipt
are authored in this repository.

## Exact computation

The checker reuses the source-exact row constructor and the general weighted
determinant engine validated by the `Phi_3` checkpoint.  It cancels
Pochhammer denominators term by term in `Z[p]`, extracts every entry's exact
`Phi_4` order and leading residue, and computes the signed minimum determinant
coefficient with `O(N 2^N)` subset states.  The decisive calculation remains
coefficientwise in `mu`; `mu=0,1` are exact regression specializations.

## All-index first-appearance support count

At rank `N=2d+1`, the number of minimum-`Phi_d` determinant assignments is
exactly

`(d+1) 2^d`.

This explains the observed counts `4,12,32,80` for `d=1,2,3,4` and is an
all-`d` combinatorial identity, not an extrapolation.

Split the indices into

`A={0,...,d-1}`, `B={d,...,2d-1}`, and `C={2d}`,

and write a member of `B` as `d+r`, `0<=r<d`.  The exact residual exponent
formula shows:

- zero-weight `B_r -> A_a` and `A_a -> B_r` edges exist exactly when
  `a+r<d`;
- every `C <-> A` edge has weight zero;
- the weight-one positive-to-positive edges are every edge incident to `C`
  and the edges `B_r -> B_s` with `r+s<d`.

A total-weight-one permutation selects exactly one of those positive-to-
positive edges.  The remaining positive rows match all `A` columns through a
Ferrers matrix, and the remaining `A` rows match the positive columns through
its transpose.  If the removed positive vertex is `C`, the Ferrers matching
count is `1`; if it is `B_r`, the count is `2^r`.  Hence the total number is

`1 + 2 sum_(r<d)2^r + sum_(r+s<d)2^(r+s)`

`= (2^(d+1)-1) + (1+(d-1)2^d)`

`= (d+1)2^d`.

Thus the rank-nine computation below decides cancellation among exactly 80
fully classified minimum assignments.  The count alone says nothing about
their signed quotient-ring sum; that is the discriminating residue probe.

## Exact result

The coefficientwise subset-DP calculation gives

`sum_(minimum assignments) sign(sigma) prod_i residue(i,sigma(i))`

`= -1655261568` in `Q[mu,p]/(p^2+1)`.

This is a nonzero constant: all `mu`-dependent terms cancel, but the complete
minimum layer does not.  The exact minimum permutation order is one, equal to
the forced residual-border order, so the rank-nine determinant has precisely
one `Phi_4` factor after the scalar content is removed.  The `mu=0` and `mu=1`
specializations reproduce the same residue; at `mu=0` the zero `(0,0)` entry
is treated as an absent determinant edge and does not change the result.

Consequently, parameter tuning cannot produce a second `Phi_4` copy at first
appearance.  This eliminates minimum-layer `Phi_4` cancellation as the
missing height mechanism and makes an unstructured higher-rank `Phi_4` audit
non-progress.  Any continuation must instead supply an all-rank residue-class
identity or move to a structurally different cyclotomic or integral mechanism.

## Decision boundary

- A nonzero residue proves exact rank-nine `Phi_4` order one and eliminates
  minimum-layer cancellation at its first appearance.
- A zero residue proves a genuine second `Phi_4` factor and opens the next
  associated-graded layer.

The computation realizes the first branch.

Neither outcome is an all-rank content theorem or an irrationality proof.
After the first-appearance decision, a larger rank is not progress without a
new residue-class mechanism.

## Reproduction

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_phi4_associated_graded.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_phi4_associated_graded_receipt.json
```
