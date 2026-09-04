# Zudilin endpoint recurrence lab

## Targeted invariant

The exact `d=1,...,5` boundary-form computation predicts more than
noncancellation.  If `X_d` is the zero-weight `d x (d+1)` cross block, its
cofactor/null vector should have the form

`v_d=(v_0,0,...,0,v_d)`.

Writing `rho_d=-v_0/v_d`, this is equivalent to the exact column recurrence

`last_column(X_d)=rho_d first_column(X_d)`

together with full row rank after an endpoint column is removed.

For the weight-one border corners, the observed recurrence is

`Z_(0,d)=(11/4) rho_d Z_(0,0)`,

`Z_(d,d)=(50/3) rho_d^2 Z_(0,0)`.

These identities imply

`6 (-1)^d Res_d = 73 v_0^2 Z_(0,0)`.

Thus uniform first-appearance noncancellation would follow from endpoint
support, the two fixed ratios, and nonvanishing of one triangular cofactor and
one local border entry.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction and analytic
`q`-order estimate are due to Wadim Zudilin, *On the irrationality of
generalized q-logarithm*, Research in Number Theory 2 (2016), Article 15,
DOI [10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).
The downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the endpoint recurrence, the composite-index cyclotomic tests,
or the factor-`73` contraction recorded here.  Those source-row identities and
their finite replays are authored in this repository.

## Discriminating computation

This checker targets `d=6` and `d=7` for distinct reasons:

- `d=6` tests the recurrence at a new composite index;
- `d=7` enters the first degree-six cyclotomic field.

It does not compute the full `(d+1)2^d` minimum assignment sum.  It constructs
only the moment strip `d<=n<=3d` plus `n=4d`, computes the rectangular maximal
minors, and checks the named column and corner identities in `Q[p]/(Phi_d)`.
When they hold, the generic bordered identity gives the exact implied first-
appearance residue without an exponential determinant replay.

## Composite-index result

At `d=6`, every named identity survives exactly in
`Q[p]/(p^2-p+1)`:

- the cofactor vector is supported only at its two endpoints;
- `rho_6=3(p-1)` and the last cross column is `rho_6` times the first;
- the corner ratios are exactly `11 rho_6/4` and `50 rho_6^2/3`; and
- `6 Res_6=73 T_00` with `T_00` nonzero.

The implied rank-thirteen first-appearance residue is

`-21720342295296`

times

`27854892322826692248697 p + 14007634530523353294814`,

which is a nonzero representative of degree one.  This decides the layer
without summing its 448 minimum assignments.  Composite cyclotomic index is
therefore not the missing obstruction to the recurrence.

## Degree-six result

At `d=7`, the same identities survive in the first degree-six quotient
`Q[p]/(p^6+p^5+p^4+p^3+p^2+p+1)`.  The endpoint multiplier is

`rho_7=-3(p^4+1)`.

The cofactor vector again has no interior support, both fixed corner ratios
hold, and the factor-73 identity gives a nonzero representative of degree five
for the implied rank-fifteen residue.  This decides the layer without its
1,024 minimum assignments.

The `q`-Lucas regressions cover 465 valid block/residue cases at `d=6` and 630
at `d=7`, with zero mismatches.  The endpoint mechanism has therefore survived
indices `1,...,7`, a new composite index, and residue-field degrees
`1,2,4,6`.  More indices are not the next step: the evidence now specifically
licenses reduction of the three displayed source-row identities.

## Analytic route

At a primitive `d`-th root, write every source index as `n=qd+s`.  The fixed
quotients `q=1,2,3,4` in this probe and the constants `11/4`, `50/3` point to a
root-of-unity `q`-Lucas decomposition of the Gaussian-polynomial source rows.
Survival at both target indices licenses that proof route; failure localizes
the first missing residue-class term.

In source-row language, the endpoint recurrence is equivalent to a multiplier
`K_d` independent of `s` such that

`S_(2d+s)=K_d S_(d+s)` for `0<=s<d`,

where `S_n` is the scalar-unit-weighted primitive residue.  The two corner
identities then become

`S_(3d)=(11/4)K_d S_(2d)`,

`S_(4d)=(50/3)K_d^2 S_(2d)`.

These are the exact three statements the `q`-Lucas decomposition must prove;
no general determinant remains in the target.

For the exact prime indices `d=2,3,5,7`, the multiplier further simplifies to

`K_d=12 d^3 (p-1)^3 mod Phi_d`.

The new composite case `d=6` preserves all endpoint and corner identities but
has a different cyclotomic-unit multiplier.  Thus the constants `11/4`,
`50/3`, and `73` belong to the universal quotient-block limit, while `K_d`
also carries arithmetic from the scalar unit.  A proof should separate these
two layers rather than assume a prime formula at composite indices.

There is a useful source simplification.  The previously proved identity
`coefficient_mu(R_n)=0` for `n>=d` means the local residue may be evaluated at
the actual Lambert value without retaining that value: the `A_n` term already
vanishes modulo `Phi_d`.  One may therefore use Zudilin's closed
hypergeometric expression for `v_n(ell_p)` rather than separately reducing the
`B_n` and `C_n` sums.  At `x=z=1`, the root-of-unity limit of

`(q;q)_n^4/(q^(n+1);q)_(n+1) * 2phi1(...)`

after the known scalar extraction is the natural place to apply `q`-Lucas.
Only quotient blocks `q=1,2,3,4` occur in the three recurrence statements, so
the constants `1`, `11/4`, and `50/3` should arise from a finite block-level
limit rather than from an unbounded determinant calculation.

The checker separately replays the exact `q`-Lucas congruence

`[ad+b choose rd+s]_p = binomial(a,r) [b choose s]_p mod Phi_d`

for every valid residue pair `0<=b,s<d` and every quotient block `0<=a<=4`
used here.  This does not prove the full source recurrence—the Pochhammer
orders and the terminating hypergeometric sum must still be reduced—but it
certifies the finite root-of-unity decomposition on which that proof route
depends.

## `Phi_1` kernel microcosm

The fixed corner constants are exactly the first relevant moments of the
all-rank `Phi_1` kernel already isolated in the preceding checkpoint.  Put

`m_q=(q!)^3 H_q`.

Then

`m_2=12`, `m_3=396`, and `m_4=28800`,

while the universal corner triple is

`(-3m_2, (3/4)m_3, -(3/16)m_4)=(-36,297,-5400)`.

The endpoint ratio `(3,1)` contracts this fixed binary form to

`9(-36)+6(297)-5400=-3942=-54*73`.

This identifies the factor `73` and the ratios `11/4`, `50/3` with the
harmonic-moment kernel rather than an accidental run of cyclotomic residues.
The prospective all-`d` proof is therefore a root-of-unity block-collapse
theorem from Zudilin's local source rows to the `Phi_1` microcosm, followed by
the already explicit two-dimensional contraction.

## Reproduction

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_endpoint_recurrence.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_endpoint_recurrence_receipt.json
```
