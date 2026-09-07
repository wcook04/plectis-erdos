# Zudilin primitive residual border-charge lab

## One-way result

Write `H_n=P_n^3/L_n` for the scalar row factor isolated in
`ZudilinScalarContentLab.md`, and divide the Hankel entry of index `i+j` by
`H_i H_j`.  For every cyclotomic polynomial `Phi_d`, every entry of this
primitive residual matrix in the southeast block `i,j>=d` is still divisible
by `Phi_d`.  Consequently the rank-`N` primitive residual determinant contains
the new all-rank factor

`prod_(1<=d, 2d<N) Phi_d(p)^(N-2d)`.

This opens the source-facing residual factor anticipated by
`SoutheastBlockDeterminant.lean`, but also settles its first-order sufficiency
in the negative.  Its degree is at most `N^3`; together with the scalar ceiling
`N^3-N`, the total is at most `2N^3-N`, strictly below the explicit charge
required at `p=3/2`.  Thus merely multiplying all universally forced
first-order southeast-block factors cannot prove irrationality.  A surviving
Hankel route cannot obtain more merely by nesting the same entry valuations:
the valuation assignment bound is now proved sharp.  It needs genuine
determinant cancellation or a different integral model.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery used by this residual
model, is due to Wadim Zudilin, *On the irrationality of generalized
q-logarithm*, Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the residual southeast-block factor, the sharp valuation bound,
or the degree comparison at `p=3/2` recorded here.  Those residual reductions,
finite replays, and the negative route conclusion are authored in this
repository.

## Exact residual exponent

The exponent of `Phi_d` in `H_n` is

`e_d(n)=max(3 floor(n/d)-1,0)`.

When `i,j>=d`, all three active exponents are on their positive branch, so the
residual exponent is

`r_d(i,j)=e_d(i+j)-e_d(i)-e_d(j)`

`=1+3(floor((i+j)/d)-floor(i/d)-floor(j/d))`.

The parenthesis is the carry produced by adding the residues of `i` and `j`
modulo `d`, hence is either zero or one.  Therefore `r_d(i,j)` is exactly `1`
or `4`, in particular it is positive throughout the southeast block.

The generic theorem `det_southeastBlock_dvd` now applies: a `Phi_d`-divisible
southeast block starting at index `d` forces `Phi_d^(N-2d)` into the
determinant.  Multiplication over the pairwise coprime cyclotomic polynomials
gives the displayed factor.

## The entry-valuation bound is exact

The southeast-block argument is not merely a coarse lower bound on the
valuation assignment problem.  Fix `d` with `2d<N`.  Every permutation selects
at least `N-2d` entries with both indices at least `d`, and every such entry has
order at least one, so every determinant term has `Phi_d`-order at least
`N-2d`.

An explicit permutation attains equality.  Reverse the first `2d` columns.
For these rows `i+j=2d-1`, and the exact exponent formula gives order zero.
On the remaining consecutive tail, sort the row residues modulo `d` upward
and the column residues downward, then pair them.  The tail residue multiset
contains complete copies of `0,...,d-1` followed by one initial segment.  Its
oppositely sorted pairs therefore have residue sum at most `d-1`, so every tail
entry has order exactly one.  There are `N-2d` tail entries.

Explicitly, if the tail length is `qd+s`, the count of residues at most `t` is
`q(t+1)+min(s,t+1)`.  Applying this formula to the `k`-th smallest residue and
the `k`-th largest residue gives their sum at most `d-1`; the only inequality
needed is `s-min(s,t)<=min(s,d-t)`, split according as `s<=t` or `t<s<=d`.

Hence the minimum `Phi_d`-order among determinant permutation terms is exactly
`N-2d`.  No argument using only the entrywise cyclotomic valuations can force a
larger power.  Any extra determinant content must come from cancellation among
the minimum-order terms modulo `Phi_d`, which is a genuinely different
mechanism.

## Charge ceiling

The exact degree of the border factor is

`B_N=sum_(1<=d, 2d<N) phi(d)(N-2d)`.

For the decisive comparison, the deliberately loose bound `B_N<=N^3` is
enough: use `phi(d)<=d`, `N-2d<=N`, and
`sum_(d<N/2)d<=sum_(d<N)d<N^2`.  Combining it with the already proved scalar ceiling gives total
extracted degree at most `2N^3-N`.  For every integer `N>=2`,

`41(2N^3-N) < 39(4N^3-3N^2)`.

The positive difference is

`N(74N^2-117N+41)`.

Writing `N=x+2` with `x>=0`, the quadratic becomes
`74x^2+179x+103`, which is positive.  The two corresponding Lean theorems in
`AdelicHeightBridge.lean` check both this strict ceiling and its monotone
consumer for an arbitrary proposed extracted degree.

## Exact symbolic checkpoints

The checker constructs the primitive residual determinant directly from the
primary-source rows.  At rank three its cyclotomic content beyond the scalar
factor is `Phi_1`; at rank four it is exactly `Phi_1^2`.  The rank-four content
signature is `p^30 Phi_1^2`, with unaccounted quotient `1`.  The `p`-power is
reported separately and is not part of this cyclotomic charge claim.  These
finite factorizations confirm the all-rank forced factor at the first
discriminating ranks and expose no accidental extra primitive factor; the
all-rank claim itself comes from the exponent identity and determinant lemma.

Rank five is now exact without expanding the full bivariate determinant.
Evaluate it at `mu=0` and `mu=1`; the two univariate determinants have degrees
`320` and `331`, and their gcd is exactly

`p^55 (p-1)^3 (p+1) = p^55 Phi_1^3 Phi_2`.

The gcd of the bivariate determinant's `mu`-coefficients divides the gcd of
every pair of specializations, while the all-rank border theorem forces
`Phi_1^3 Phi_2` into every coefficient.  After saturating the separately
accounted monomial `p`, the two bounds coincide.  Therefore rank five has no
additional primitive non-`p` content.  The reusable helper
`system/lib/formal_math_polynomial_content.py` packages this specialization-
sandwich method so later determinant experiments can avoid explosive full
multivariate expansion while retaining an exact algebraic conclusion.

Run or replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_residual_border_charge.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_residual_border_charge_receipt.json
```

The durable receipt binds this analysis, the source formulas, the scalar
checker, and both Lean consumers by digest.  Erdős #1049 remains open.
