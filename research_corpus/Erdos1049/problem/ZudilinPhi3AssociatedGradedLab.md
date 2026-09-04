# Zudilin rank-seven `Phi_3` associated-graded lab

## Mechanism question

The residual-border theorem forces

`Phi_d(p)^(N-2d)`

into the primitive rank-`N` Hankel determinant whenever `2d<N`.  Exact
rational-root computations show that the minimum layers for `Phi_1` and
`Phi_2` do not cancel at rank six.  They do not decide the first genuinely
non-rational cyclotomic quotient: `Phi_3=p^2+p+1` first has positive forced
order at rank seven.

This probe asks a binary question in the exact residue field
`Q[mu,p]/(p^2+p+1)`: after extracting every entry's `Phi_3` valuation, does
the signed sum of all determinant terms of minimum total weight vanish?  A
zero opens a deeper cyclotomic-content mechanism invisible to entry
valuations.  A nonzero residue proves the determinant order is exactly the
forced order one at this first possible rank.

This changes the cyclotomic field and residue-class geometry; it is not a
rank-seven extension of the earlier `p=1` or `p=-1` evaluations.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery reused by this
probe, is due to Wadim Zudilin, *On the irrationality of generalized
q-logarithm*, Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the `Phi_3` rank-seven minimum-layer count, the residue
`25863462 (p-1)`, or the exact noncancellation decision recorded here.  Those
associated-graded reductions, finite replays, and their exact receipt are
authored in this repository.

## Exact computation

The checker reconstructs the source rows in `Z[p]` by cancelling the primary
Pochhammer denominators term by term.  This is algebraically identical to the
reference rational-expression constructor—the two agree exactly through the
regression range—but it avoids global rational simplification of large source
expressions.

For each primitive residual entry it then records:

1. the exact number of `Phi_3` divisions;
2. the first nonzero quotient residue modulo `Phi_3`; and
3. whether a specialization makes the entire entry zero.

Identically zero specialized entries are absent assignment edges, not errors
and not zero-valued leading coefficients.  The shared
`formal_math_tropical_determinant` engine handles these edges explicitly.

The determinant layer is computed by subset dynamic programming.  A state is
the set of columns already used; for each state the engine retains only the
least accumulated valuation, the number of assignments attaining it, and
their exact signed coefficient in the caller's quotient ring.  This costs
`O(N 2^N)` states rather than enumerating `N!` permutations and preserves
genuine cancellation exactly.

The decisive run is coefficientwise in `mu`.  The `mu=0` and `mu=1` runs are
independent specializations used to expose zero-entry semantics and check the
coefficientwise result, not substitutes for it.

## Result

The coefficientwise minimum layer does not cancel.  Its exact residue is

`25863462 (p-1)` in `Q[mu,p]/(p^2+p+1)`.

This is nonzero because `p-1` is not divisible by `p^2+p+1`.  The minimum
permutation weight is the forced value `1`, and exactly `32` determinant
assignments attain it.  Therefore the primitive rank-seven determinant has
exact `Phi_3` order one: minimum-term cancellation supplies no second copy of
`Phi_3` at the first rank where the border theorem forces one.

Both specializations give the identical residue.  At `mu=0`, the `(0,0)`
entry vanishes identically and is correctly removed as an assignment edge;
the remaining graph still has the same 32 minimum assignments and the same
signed residue.  At `mu=1` there are no zero entries.  The coefficientwise
calculation has no zero entries and proves directly that the result is
independent of `mu`, rather than inferring that fact from the two samples.

This decisively eliminates the first non-rational-root minimum-cancellation
mechanism.  It does not establish an all-rank `Phi_3` identity.  Any successful
extra-content route must now use a new residue-class theorem at unbounded
rank, a different cyclotomic family, a higher associated-graded layer opened
for some structural reason, or a different integral model.  A blind rank-eight
extension would not change that obligation.

## Decision boundary

- A nonzero coefficientwise residue proves exact rank-seven `Phi_3` order one
  and eliminates minimum-layer cancellation at the first positive rank.
- A zero coefficientwise residue proves a genuine extra `Phi_3` factor and
  opens computation of the next associated-graded layer.

Either conclusion is finite-rank and cyclotomic-specific.  It does not prove
an all-rank content theorem or irrationality of the Lambert value at `3/2`.
After this decision, increasing the rank at `Phi_3` is not licensed without a
new residue-class identity.

## Reproduction

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_phi3_associated_graded.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_phi3_associated_graded_receipt.json
```
