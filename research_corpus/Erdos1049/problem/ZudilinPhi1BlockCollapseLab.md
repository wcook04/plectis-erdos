# Zudilin root-of-unity block-collapse lab

## Exact target

Let `S_n^(d)` be the leading `Phi_d` residue of the cleared inhomogeneous
source row `-B_n-C_n`, after removal of the forced scalar power

`e_d(n)=3 floor(n/d)-1`

for `n>=d`.  Equivalently, if `R_n` is the primitive row residue and `U_n` is
the scalar cyclotomic unit, then

`S_n^(d)=U_n R_n` in `Q[p]/(Phi_d)`.

The endpoint recurrence suggested a stronger identity.  Put

`K_d=S_(2d)^(d)/S_d^(d)`

and

`c_q=(q!)^3 H_q/12^(q-1)`.

The strong block-collapse target is that the two inhomogeneous source channels
obey, separately and with the same multiplier,

`S_(qd+s)^(d)=K_d^(q-1) c_q S_(d+s)^(d)`

for every residue class `0<=s<d`; their sum then obeys the same identity.  The
three quotient blocks needed by the first-appearance determinant have

`c_2=1`, `c_3=11/4`, and `c_4=50/3`.

The computation targets one further simplification on the same complete
strip:

`B_n^(d)=2 C_n^(d)`.

Together, the two identities make the full inhomogeneous source residue
`S_n^(d)=3 C_n^(d)`.  An all-`d` proof would therefore need to reduce only one
terminating source sum; no cancellation between `B` and `C` remains available.

This is strictly stronger than the endpoint and corner identities.  The
`q=2` strip gives the entire last-column recurrence, not just its induced
cofactor support.  The `s=0`, `q=3,4` cases give the two fixed border-corner
ratios.  Consequently the committed two-dimensional boundary contraction and
its factor `73` follow from this one source-row law.

## Discriminating computation

The checker constructs every `S_n^(d)` with `d<=n<5d` directly in the bounded
local quotient, and tests both source channels and their sum at all `3d`
quotient/residue pairs for each selected `d`.  Its canonical range is
`d=1,...,5`, so it contains 45 exact positions and 135 separately recorded
channel/combined comparisons.  The `d=5` strip is the new degree-four test;
failure in any one channel entry kills strong block collapse and leaves the
weaker endpoint recurrence as the correct target.

The computation also requires that `S_d` and `K_d` are nonzero, rechecks the
all-index disappearance of the `mu` coefficient over the complete source
strip, and replays the finite `q`-Lucas congruence through quotient block four.
These checks keep the inferred ratios from hiding a zero denominator or an
incorrect root-of-unity reduction.

## Exact result

Every canonical identity survives.  Across `d=1,...,5`, all 45
quotient/residue positions and all 135 separately recorded `B`, `C`, and
combined comparisons are exact in `Q[p]/(Phi_d)`.  At every selected index:

- the two channel multipliers equal the combined `K_d`;
- `B=2C` on the complete source strip `d<=n<5d`;
- the source base and multiplier are nonzero; and
- the primitive `mu` coefficient vanishes throughout the strip.

The exact multipliers are

`K_1=12`, `K_2=-768`, `K_3=972(2p+1)`,

`K_4=-6144`, `K_5=1500(p-1)^3`.

The degree-four `d=5` quotient is therefore not an obstruction.  The 725
finite `q`-Lucas regression cases through quotient block four also have zero
mismatches.  The local computation never exceeds modulus degree 48.

This is a one-way opening rather than a proof by sampling: it eliminates
cross-channel cancellation as the observed mechanism and reduces the all-`d`
target to one explicitly supported terminating sum.  The finite range does
not promote the resulting block law to an all-`d` theorem.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery, is due to Wadim
Zudilin, *On the irrationality of generalized q-logarithm*, Research in
Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the complete-strip channel identities, the `B=2C` specialization,
the factorial-harmonic block multipliers, or the factor-`73` boundary
contraction recorded here.  Those finite replays, source-row reductions, and
the all-`d` proof target are authored in this repository.

## Source support behind the identity

The local source formula already narrows the prospective proof.  Write

`n=qd+s`, `k=ad+b`, with `0<=b,s<d`.

In a `B` summand before its harmonic denominator is removed, the exact
`Phi_d` order of the common product is

`3q + [b+s>=d] + [b>s]`.

The target order is `3q-1`.  Therefore a `B` term can survive only when its
denominator index is a multiple of `d` and

`0<=b<=min(s,d-1-s)`.

For `C`, the denominator must instead satisfy `ell congruent s (mod d)`.
The two Gaussian factors then survive `q`-Lucas only for the complementary
residue window

`max(0,2s-d+1)<=b<=s`.

Thus neither source sum retains an unrestricted two-dimensional lattice at a
primitive root.  Each collapses to a finite residue window and a quotient
sum.  The remaining analytic obligation is precise: factor the common
residue kernel from those two windows and prove that their combined quotient
sum is

`K_d^(q-1) (q!)^3 H_q/12^(q-1)`.

This support calculation also explains why the `A_n mu` channel cannot repair
a failure: its order is at least `3q`, one above the leading layer, for every
`a,b`.

## Analytic consequence

If all canonical strips survive channel by channel and satisfy `B=2C`,
cancellation between the two sums is decisively eliminated and the analytic
target reduces to the finite quotient/residue decomposition of either one.
Further index sampling is then not the next move.  One should split by
`k=ad+b`, apply `q`-Lucas to the Gaussian factors, extract the multiples of
`d` from the Pochhammer products, and evaluate the remaining quotient sum by
the same Legendre/harmonic identities that produced the all-rank `Phi_1`
kernel.

That route would prove first-appearance noncancellation for every cyclotomic
index: block collapse supplies the universal `2 x 2` boundary form, and the
already proved contraction makes its residue a nonzero multiple of `73`.
This still would not by itself prove the full denominator charge or the
irrationality of the Lambert value; it would remove the expanding homogeneous
boundary-cancellation mode from the residual determinant.

## Reproduction

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_phi1_block_collapse.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_phi1_block_collapse_receipt.json
```

Independent raw results can be produced with `--cyclotomic-index`,
`--result-output`, and `--result-only`, then combined with repeated
`--from-result` arguments.  The canonical receipt embeds hashes of this note,
the local source adapter, the generic cyclotomic engine, and the analytic
consumer.
