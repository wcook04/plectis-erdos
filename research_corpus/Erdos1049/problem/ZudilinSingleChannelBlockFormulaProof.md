# Zudilin all-`d` single-channel block formula

## Theorem

Fix `d>=1`, a primitive `d`-th root `zeta`, and write

`n=qd+s`, `q>=1`, `0<=s<d`.

Let `C_n^(d)` denote the leading `Phi_d` residue of Zudilin's cleared `C`
source after removal of the forced power

`Phi_d^(3 floor(n/d)-1)`.

Put

`M_d(zeta)=((p^d-1)/Phi_d(p)) at p=zeta`

and

`K_d=12 d^3 M_d(zeta)^3` in `Q(zeta)`.

Then

`C_(qd+s)^(d)
 =K_d^(q-1) ((q!)^3 H_q/12^(q-1)) C_(d+s)^(d)`.

The all-index channel theorem in `ZudilinChannelDivisibilityProof.md` gives
`B_n^(d)=2C_n^(d)`.  Therefore the same block formula holds for the full
inhomogeneous leading source

`S_n^(d)=-B_n^(d)-C_n^(d)=-3C_n^(d)`.

This proves the source-row block-collapse identity for every cyclotomic index,
every quotient block, and every residue class.  The proof is authored
mathematics with exact executable regressions; it is not yet formalized in
Lean.

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
**not** state the all-index single-channel block formula, the root-product
identity `M_(jd)(zeta)=j M_d(zeta)`, the factorial-harmonic multipliers, or the
first-block rank/corner contraction recorded here.  Those source-row
identities, their finite replays, and the conditional noncancellation boundary
are authored in this repository.

## 1. Leading `C` residue from pole separation

Use the notation of the channel-divisibility proof:

`P_n=product_(1<=r<=n)(p^r-1)`

and

`Ctilde_n=p^(n+1)P_n^3
  sum_(r=1)^n C_(n,r)(p)/(p^r-1)`.

At `p=zeta`, only `r=jd`, `1<=j<=q`, contribute to the leading
`Phi_d^(3q-1)` coefficient.  The proved `q`-Lucas separation says

`C_(n,jd)(zeta)=kappa_(d,s,q) C_(q,j)(1)`.

Coefficient extraction gives `C_(q,j)(1)=1` for every `j`.  Hence the pole
coefficient is the same `kappa_(d,s,q)` in every quotient position.

Define

`L_(d,s,q)=((P_(qd+s)/Phi_d^q) at p=zeta)`.

Also put

`M_(jd)(zeta)=((p^(jd)-1)/Phi_d(p)) at p=zeta`.

Differentiating the numerator at the simple root gives

`M_(jd)(zeta)=jd zeta^(-1)/Phi_d'(zeta)=j M_d(zeta)`.

It follows directly from the cleared `C` sum that

`C_(qd+s)^(d)
 =zeta^(qd+s+1) L_(d,s,q)^3
  kappa_(d,s,q) H_q/M_d(zeta)`.

The harmonic number appears because the `j`-th pole contributes
`1/M_(jd)=1/(jM_d)`.

## 2. Quotient-block product

Compare `L_(d,s,q)` with the first block `L_(d,s,1)`.  For each nonzero
residue `1<=b<d`, the product `P_(qd+s)` has exactly `q-1` more factors
congruent to `b` modulo `d` than `P_(d+s)`.  Their root-of-unity product is

`A_d=product_(b=1)^(d-1)(zeta^b-1)`.

For the multiples of `d`, the extra divided factors are

`M_(2d),...,M_(qd)=2M_d,...,qM_d`.

Therefore

`L_(d,s,q)/L_(d,s,1)
 =(A_d M_d)^(q-1) q!`.

The residue factor from the preceding proof has phase

`(-1)^(q(d-1)+s+b) zeta^(b(b+1)/2)`.

Its Gaussian part is independent of `q`, so

`kappa_(d,s,q)/kappa_(d,s,1)
 =(-1)^((q-1)(d-1))`.

This statement does not require division by a possibly zero `kappa`: it is an
identity between the two finite sums, and can be substituted multiplicatively
in the leading-source formula.

Finally `zeta^((q-1)d)=1`.  Dividing the leading formula by its first-block
version gives

`C_(qd+s)^(d)/C_(d+s)^(d)
 =[(-1)^(d-1)(A_dM_d)^3]^(q-1)(q!)^3H_q`.

Again, this quotient notation abbreviates a multiplicative identity and does
not assume the first-block source is nonzero.

## 3. Closed multiplier

Because `zeta^b`, `0<=b<d`, are all `d`-th roots of unity,

`product_(b=1)^(d-1)(1-zeta^b)=d`.

Thus

`A_d=(-1)^(d-1)d`.

The sign in the block factor cancels its cube:

`(-1)^(d-1)(A_dM_d)^3=d^3M_d^3`.

Defining

`K_d=12d^3M_d^3`

therefore yields

`C_(qd+s)^(d)
 =K_d^(q-1)((q!)^3H_q/12^(q-1))C_(d+s)^(d)`.

The multiplier is nonzero.  The cyclotomic polynomial has a simple root at
`zeta`, so `M_d(zeta)=d zeta^(-1)/Phi_d'(zeta)` is nonzero.

For prime `d`, `M_d(zeta)=zeta-1`, recovering the previously observed formula

`K_d=12d^3(zeta-1)^3`.

For composite `d`, `M_d` retains the proper cyclotomic factors.  This explains
the formerly exceptional-looking values

`K_4=-6144`,

`K_6=-62208(2p-1) mod Phi_6`.

They are not exceptions; they are exact instances of the same proper-factor
formula.

## 4. Boundary consequence and remaining obstruction

The cases used by the first positive-border determinant are

`q=2: (q!)^3H_q/12^(q-1)=1`,

`q=3: (q!)^3H_q/12^(q-1)=11/4`,

`q=4: (q!)^3H_q/12^(q-1)=50/3`.

Thus the last cross column is uniformly proportional to the first, and the
two positive-border corners have the fixed `11/4` and `50/3` ratios for every
`d`.  Quotient-block growth and residue-dependent correction terms can no
longer produce an expanding homogeneous boundary mode.

One exact obstruction remains before all-`d` first-appearance
noncancellation: the first-block `d x d` cross matrix must be nonsingular.
If it is, the rectangular cofactor vector is supported at its two endpoints;
the bordered determinant identity then contracts the fixed binary form to the
nonzero factor `73`.  If it is singular, the first singular `d` supplies an
exact countermechanism.  This rank decision, rather than another block or
cyclotomic horizon, is the next target.

The block theorem does not supply the missing asymptotic denominator charge
or prove irrationality of the Lambert value at `3/2`.

## Executable regression

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_single_channel_block_formula.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_single_channel_block_formula_receipt.json
```

The checker reconstructs `A_d`, `M_d`, and `K_d` in the cyclotomic quotient.
It exactly matches all committed source multipliers for `d=1,...,7`, including
composite `d=4,6`; replays the root-product identity through `d=10`; and
checks the normalized factorial-harmonic constants through quotient block 12.
The canonical receipt content-hash binds the prior all-index pole proof, the
finite source receipts, this argument, and the existing analytic consumer.
