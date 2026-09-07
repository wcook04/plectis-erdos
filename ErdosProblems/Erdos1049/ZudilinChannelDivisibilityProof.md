# Zudilin all-index channel-divisibility proof

## Theorem

For `n>=1`, put

`P_n(p)=product_(1<=r<=n)(p^r-1)`.

At `x=z=1`, Zudilin's cleared inhomogeneous source coefficients satisfy

`p^(n+1) P_n(p)^3 | Btilde_n(p)-2 Ctilde_n(p)` in `Z[p]`.

Consequently, for every `d<=n`, the leading residues after removal of the
forced scalar power `Phi_d^(3 floor(n/d)-1)` satisfy

`B_n^(d)=2 C_n^(d)`.

This is an authored all-index argument.  The executable receipt checks each
source reduction through the ranges stated below, but the universal
quantifiers come from the algebra in this note.  The theorem is not yet
formalized in Lean.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction and its analytic
`q`-order estimate are due to Wadim Zudilin, *On the irrationality of
generalized q-logarithm*, Research in Number Theory 2 (2016), Article 15,
DOI [10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).
The downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  That source
does **not** state the all-index channel divisibility or the specialized
cyclotomic residue identity above.  Those universal source reductions and
their executable regressions are authored in this repository.

## 1. Regroup the source by its poles

Write Gaussian polynomials with base `p` as `[a choose b]_p`, and define

`T_(n,k)=(-1)^(n+k) p^(k(k+1)/2)
          [n+k choose k]_p [n choose k]_p`.

The exact source constructor gives

`Btilde_n = p^(n+1) P_n^3
  sum_(k=0)^n T_(n,k) sum_(r=1)^k 1/(p^r-1)`.

For `1<=r<=n`, put

`U_(n,r,k)=(-1)^k p^((n-k)(n-k+1)/2)
  [n choose k]_p [2n-r-k choose n]_p`

for `0<=k<=n-r`.  Replacing the original `C` index `ell` by `r=n-ell`
gives

`Ctilde_n = p^(n+1) P_n^3
  sum_(r=1)^n 1/(p^r-1) sum_(k=0)^(n-r) U_(n,r,k)`.

Hence

`Btilde_n-2Ctilde_n = p^(n+1) P_n^3 R_n(p)`,

where

`R_n(p)=sum_(r=1)^n N_(n,r)(p)/(p^r-1)`

and

`N_(n,r)=sum_(k=r)^n T_(n,k)-2 sum_(k=0)^(n-r)U_(n,r,k)`.

It remains to prove that the rational function `R_n` is a polynomial.

## 2. The correct cancellation is cyclotomic, not termwise

The tempting stronger claim `(p^r-1)|N_(n,r)` is false.  Already at `n=2`,
the remainders for `r=1,2` are

`-2`, `2(p+1)`.

Neither denominator divides its numerator, but

`-2/(p-1)+2(p+1)/(p^2-1)=0`.

Thus the proof must combine poles belonging to the same cyclotomic factor.
This exact counterexample eliminates denominator-by-denominator telescoping.

Every denominator `p^r-1` is squarefree in characteristic zero.  Fix a
primitive `d`-th root `zeta`, and write

`n=qd+s`, `0<=s<d`.

Only `r=jd`, `1<=j<=q`, have a pole at `zeta`.  Since

`(p^(jd)-1)' at zeta = jd zeta^(-1)`,

the residue of `R_n` at `zeta` is zero exactly when

`sum_(j=1)^q N_(n,jd)(zeta)/j=0`.

Proving this for every `d<=n` removes every irreducible factor of the common
denominator `L_n=product_(d<=n)Phi_d`, and therefore proves that `R_n` is a
polynomial.  Its common numerator and the monic denominator `L_n` lie in
`Z[p]`; monic polynomial division then shows that this polynomial actually
lies in `Z[p]`, not merely `Q[p]`.

## 3. `q`-Lucas separates the pole vector

Write `k=ad+b`, `0<=b<d`.  The root-of-unity `q`-Lucas identity is

`[Ad+B choose Rd+S]_zeta = binomial(A,R)[B choose S]_zeta`

when `0<=B,S<d`, with the right side zero if `S>B`.

For the `B` channel, both Gaussian factors in `T_(n,k)` survive exactly for

`0<=b<=min(s,d-1-s)`.

In that window they become

`[n choose k]_zeta=binomial(q,a)[s choose b]_zeta`,

`[n+k choose k]_zeta=
  binomial(q+a,a)[s+b choose b]_zeta`.

After the ordinary sign `(-1)^(q+a)` is removed, the remaining phase is

`epsilon_b=(-1)^(q(d-1)+s+b) zeta^(b(b+1)/2)`,

independent of `a`.  Independence follows by increasing `a` once: the new
sign is `(-1)^(d-1)` and the new root-of-unity factor is
`zeta^(d(d+1)/2)`; their product is one for both odd and even `d`.

Therefore, with

`kappa_(d,s,q)=sum_(b=0)^min(s,d-1-s)
  epsilon_b [s choose b]_zeta [s+b choose b]_zeta`,

the entire `B` pole coefficient separates as

`sum_(k=jd)^n T_(n,k)(zeta)=kappa_(d,s,q) B_(q,j)`,

where

`B_(q,j)=sum_(a=j)^q (-1)^(q+a)
  binomial(q+a,a)binomial(q,a)`.

For the `C` channel, `q`-Lucas leaves the complementary window

`max(0,2s-d+1)<=b<=s`.

Its Gaussian residue is

`[s choose b]_zeta [2s-b choose s]_zeta`.

Substitute `b=s-c`.  Then `c` runs through the `B` window and Gaussian
symmetry gives

`[s choose s-c]_zeta [s+c choose s]_zeta
 =[s choose c]_zeta [s+c choose c]_zeta`.

The remaining phase becomes

`(-1)^(q(d-1)+s-c) zeta^(c(c+1)/2)=epsilon_c`,

because the sign exponents differ by `2c`.  Thus the `C` channel has the
same factor `kappa_(d,s,q)`:

`sum_(k=0)^(n-jd) U_(n,jd,k)(zeta)=kappa_(d,s,q) C_(q,j)`,

where

`C_(q,j)=sum_(a=0)^(q-j)(-1)^a
  binomial(q,a)binomial(2q-j-a,q)`.

Consequently

`N_(n,jd)(zeta)=kappa_(d,s,q)(B_(q,j)-2C_(q,j))`.

All dependence on `d`, `s`, and `zeta` has separated into one common factor.

## 4. The ordinary vector has zero weighted sum

First, `C_(q,j)=1`.  Terms with `a>q-j` vanish, so extend the sum to `q` and
extract the coefficient of `x^q`:

`C_(q,j)
 =[x^q](1+x)^(2q-j)
   sum_(a=0)^q binomial(q,a)(-1/(1+x))^a`

`=[x^q](1+x)^(2q-j)(x/(1+x))^q`

`=[x^q]x^q(1+x)^(q-j)=1`.

Next interchange the two finite sums:

`sum_(j=1)^q B_(q,j)/j
 =sum_(a=1)^q (-1)^(q+a)
   binomial(q+a,a)binomial(q,a) H_a`.

The harmonic Legendre identity already proved in
`ZudilinPhi1AssociatedGradedKernel.md` is

`sum_(a=0)^q (-1)^a
  binomial(q+a,a)binomial(q,a)H_a=(-1)^q 2H_q`.

Multiplying by `(-1)^q` gives

`sum_(j=1)^q B_(q,j)/j=2H_q`.

Since `C_(q,j)=1`, it follows that

`sum_(j=1)^q (B_(q,j)-2C_(q,j))/j
 =2H_q-2 sum_(j=1)^q 1/j=0`.

The separated pole residue is this zero multiplied by `kappa_(d,s,q)`.
Every primitive-root pole cancels, so `R_n` is a polynomial.  Substitution in
the source regrouping proves

`p^(n+1)P_n^3 | Btilde_n-2Ctilde_n`

for every `n>=1`.

## 5. Leading-layer consequence

For `d<=n`, `P_n^3` contains `Phi_d^(3 floor(n/d))`.  The forced scalar row
content contains only `Phi_d^(3 floor(n/d)-1)`.  Dividing the channel
difference by that scalar content leaves at least one `Phi_d`, hence

`B_n^(d)=2C_n^(d)`

on every leading cyclotomic layer.  The full inhomogeneous source is therefore

`-B_n^(d)-C_n^(d)=-3C_n^(d)`.

This kills channel imbalance and cross-channel cancellation as all-index
boundary mechanisms.  It does not prove the remaining single-channel block
law.  The next analytic target is now exact: apply the same residue-window
factorization to `C_(qd+s)` itself and prove the quotient constants

`1`, `11/4`, `50/3`

uniformly in `d` and `s`.  Combined with the committed endpoint contraction,
that would kill first-appearance boundary cancellation for every cyclotomic
index.

## Executable regression

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_pole_separation.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_pole_separation_receipt.json
```

The checker verifies the ordinary coefficient-extraction and harmonic
identities through quotient block 12.  It constructs exact `B`, `C`, and
difference pole vectors for every residue class at `d=1,...,5` and quotient
blocks `2,3,4`, and verifies their common `q`-Lucas separation and zero
weighted residue.  It also records the `n=2` counterexample to the stronger
termwise telescope.  Source, analysis, prior receipts, and the existing height
consumer are content-hash bound in the canonical receipt.
