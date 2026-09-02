# Zudilin all-rank `Phi_1` associated-graded kernel

## One-way mechanism result

The minimum `Phi_1=p-1` layer of the primitive residual Hankel determinant is
independent of the Padé parameter `mu` at every rank.  Consequently an extra
`Phi_1` factor can never arise from tuning `mu` or from cancellation between
the `mu` channel and the two inhomogeneous source channels.  Any all-rank
extra order would have to be an intrinsic identity in a single explicit
factorial-harmonic Hankel sequence.

More precisely, put

`lambda_n = lcm(1,...,n)`, `h_n = 1+1/2+...+1/n`,

with `lambda_0=1` and `h_0=0`, and define

`m_n=(n!)^3 h_n`.

For rank `N>=2`, let `L_N` be the signed coefficient of the minimum power
`(p-1)^(N-2)` in the determinant after the source scalar row-and-column
content has been removed.  Then

`L_N = (-3)^N (prod_(i=1)^(N-1) d_i^2)
       det_(0<=i,j<N)(m_(i+j))`,

where `d_i=(-1)^i lambda_i/(i!)^3`.  In particular `L_N` contains no `mu`.
The nonzero rank-three through rank-six computations are exact regressions of
this identity, but the identity itself is all-rank source algebra.

This eliminates a mechanism; it does **not** prove that the displayed Hankel
determinant is nonzero at every rank.  The remaining `Phi_1` question is now
the sharply named conditional-positivity problem

`det_(0<=i,j<N)((i+j)!^3 h_(i+j)) != 0`.

Because the top-left entry is `m_0=0`, a sufficient and sign-sharp statement
is that the southeast matrix `(m_(i+j))_(1<=i,j<N)` is positive definite.  In
that case its Schur complement makes the full determinant negative, and the
observed signs of `L_N` alternate as `+,-,+,-,...`.  This positivity remains
open here and is the next analytic target; reporting more positive finite
minors would not replace it.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery used by this kernel,
is due to Wadim Zudilin, *On the irrationality of generalized q-logarithm*,
Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the `Phi_1` associated-graded limit, the `mu`-independence of its
minimum layer, the bordered determinant identity, or the conditional
positivity reduction recorded here.  Those source-limit calculations, exact
bordered algebra, finite regressions, and the explicit open-problem boundary
are authored in this repository.

## Source limit

Write `H_n=P_n^3/L_n` for the row content from
`ZudilinScalarContentLab.md`.  At `p=1`,

`H_n = c_n (p-1)^(3n-1) + higher terms`,

with

`c_n=(-1)^n (n!)^3/lambda_n` for `n>=1`, and `c_0=1`.

Now divide the cleared source form `v_n=A_n mu-B_n-C_n` by `H_n`.  For
`n>=1`, its exact constant term at `p=1` is

`q_n=(-1)^(n+1) 3 lambda_n h_n`.

There are three elementary identities behind this limit.  With

`T_(n,k)=binom(n,k)binom(n+k,k)`,

the `A` source sum gives

`sum_(k=0)^n (-1)^k T_(n,k)=(-1)^n`.

This is the value `P_n(-1)=(-1)^n` in the binomial expansion of the Legendre
polynomial.  The external clearing quotient contributes one factor `p-1`, so
the entire `A_n mu/H_n` channel vanishes at `p=1`.  This is the all-rank reason
that `mu` cannot enter the minimum layer.

For the `B` channel, the pole of `sum_(ell<=k)1/(p^ell-1)` supplies `h_k`, and

`sum_(k=0)^n (-1)^k T_(n,k) h_k = (-1)^n 2h_n`.

One proof inserts
`h_k=int_0^1(1-x^k)/(1-x) dx` into the same Legendre expansion and uses the
standard endpoint integral for `P_n`.  For the `C` channel, the inner limit is

`sum_(k=0)^ell (-1)^k binom(n,k)binom(n+ell-k,n)=1`

for `0<=ell<n`.  It is the coefficient of `x^ell` in
`(1-x)^n(1-x)^(-n-1)=1/(1-x)`.  Summing the remaining poles gives `h_n`.
After the common clearing signs are restored, `-B_n-C_n` yields the displayed
`q_n`.

## Bordered determinant identity

Let `R_(i,j)=v_(i+j)/(H_i H_j)` be a primitive residual entry.  Its leading
`Phi_1` coefficients are

`R_(0,j) -> -3 d_j m_j`,

and, for `i,j>=1`,

`R_(i,j)/(p-1) -> -3 d_i d_j m_(i+j)`.

The `R_(0,0)` entry contains `mu`, but a minimum-weight determinant
permutation never selects it: minimum order `N-2` requires one zero-order
entry from row zero, one from column zero, and `N-2` first-order southeast
entries.  Thus the signed minimum layer is the determinant of the bordered
matrix obtained by replacing `R_(0,0)` by zero.

Factoring `diag(1,d_1,...,d_(N-1))` from its rows and columns leaves exactly
`-3(m_(i+j))_(0<=i,j<N)`.  Taking determinants proves the formula for `L_N`.
It also explains the exact minimum-term count `(N-1)(N-1)!` independently:
row zero may choose any positive column and the other rows may be assigned
arbitrarily.

## Executable regression and boundary

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_phi1_kernel_identity.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_phi1_kernel_receipt.json
```

The checker verifies the three exact finite-sum identities, builds both sides
of the bordered determinant formula at the already discriminated ranks, and
records their equality.  Those computations guard the source-to-kernel
translation.  The all-rank claim comes from the displayed algebra, not from
the finite regression range.  Erdős #1049 remains open.
