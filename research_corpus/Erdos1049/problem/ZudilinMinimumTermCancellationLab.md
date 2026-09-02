# Zudilin minimum-term cancellation lab

## Mechanism question

The residual-border calculation proves

`ord_(Phi_d)(det R_N) >= N-2d`

and constructs determinant permutations of exactly that tropical weight.  The
existence of minimum-weight permutations does not decide the determinant:
their signed leading coefficients could cancel.  Such cancellation is the
only remaining way for this primitive Hankel model to gain cyclotomic charge
without changing its entries or importing a new determinant identity.

The probe therefore changes coordinates from entry valuations to the
associated graded determinant.  For `Phi_1=p-1` and `Phi_2=p+1`, it computes
every residual entry's exact Taylor-leading coefficient at `p=1` or `p=-1`
and sums the signed products over all minimum-order permutations.  One nonzero
exact specialization in the auxiliary variable `mu` proves that the
associated-graded polynomial is not identically zero; only if both `mu=0,1`
vanish does the checker escalate to the coefficientwise polynomial.

## Decision rule

- A nonzero associated-graded polynomial in `mu` proves that the determinant
  has precisely the forced `Phi_d` order, so minimum-term cancellation cannot
  supply another universal copy of that factor at the tested rank.
- An identically zero associated-graded polynomial proves genuine
  coefficientwise cancellation and opens the deeper-content mechanism.  The
  next coefficient then measures its exact extra order.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery used by this probe,
is due to Wadim Zudilin, *On the irrationality of generalized q-logarithm*,
Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the rank-six associated-graded decision, the exact minimum-layer
counts, or the signed residues recorded here.  Those tropical-layer sums,
specialization checks, and their exact receipt are authored in this repository.

Ranks three through five are regressions against the already certified exact
content.  Rank six is the first new target.  The stop boundary is the exact
rank-six decision for both rational-root cyclotomic factors; increasing the
rank without a new algebraic pattern is not licensed as progress.

## Result

There is no rank-six cancellation for either rational-root cyclotomic factor.

- For `Phi_1`, the forced order is `4`.  Exactly 600 determinant permutations
  attain that order, and their signed leading sum at both `mu=0` and `mu=1` is
  `-79795247999510945843570749824`.
- For `Phi_2`, the forced order is `2`.  Exactly 16 determinant permutations
  attain that order, and their signed leading sum at both specializations is
  `-20139015744`.

Both sums are nonzero.  Therefore the rank-six determinant has exactly the
forced `Phi_1^4 Phi_2^2` order at those specializations, and neither factor can
divide every coefficient to one additional power.  This eliminates
minimum-term cancellation as the source of extra `Phi_1` or `Phi_2` content at
the first previously undecided rank.  It does not prove an all-rank no-go or
irrationality at `3/2`; the next probe must derive an all-rank associated-graded
formula or change cyclotomic/integral mechanism, not merely request rank seven.

The computation also exposes the next analytic object.  The exact numbers of
minimum `Phi_1` permutations at ranks `3,4,5,6` are

`4, 18, 96, 600 = (N-1)(N-1)!`.

The count has an exact all-rank explanation.  For `d=1`, every residual entry
with both indices positive has `Phi_1` order one, while every entry in row zero
or column zero has order zero.  A determinant permutation has minimum order
`N-2` exactly when row zero does not map to column zero: its image is one of
`N-1` positive columns, and the remaining rows can be mapped arbitrarily in
`(N-1)!` ways.  Hence the number of minimum terms is
`(N-1)(N-1)!` at every rank.  This reduces the all-rank `Phi_1` problem to the
nonvanishing of one bordered associated-graded signed sum.  The count alone
does not prove that sum nonzero, but it replaces further enumeration by a
specific determinant identity target.

Writing the `Phi_1` associated-graded matrix in the block form
`[[a,r],[c,tD]]`, that signed sum is the coefficient of `t^(N-2)`, namely a
bordered cofactor expression `-r*adj(D)*c` (up to the fixed determinant sign
convention).  Thus the next analytic route is concrete: identify the
specialized Hankel block `D` and prove this bordered cofactor nonzero at every
rank, perhaps through a condensation recurrence or total-positivity argument.
That would eliminate `Phi_1` minimum-term cancellation all-rank; another
finite rank cannot substitute for it.

There is also a sign signal worth proving rather than extrapolating.  At
`mu=0`, the `Phi_1` leading sums at ranks `3,4,5,6` have signs
`+,-,+,-`.  Together with the Hankel origin of `D`, this makes sign-regularity
of the bordered minors a sharper candidate than an arbitrary symbolic
factorization.  A positive-moment representation for the `p=1` leading
sequence, or a condensation recurrence preserving the alternating sign,
would close the required nonvanishing in an analytic-native way.

## Reproduction

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_minimum_term_cancellation.py \
  --max-rank 6 \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_minimum_term_cancellation_receipt.json
```
