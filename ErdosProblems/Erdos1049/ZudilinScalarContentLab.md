# Zudilin scalar-content lab

## Question and outcome

Zudilin's normalized Hankel determinant at `x=z=1` has no hidden analytic
`q`-order.  The next source-native possibility is arithmetic: perhaps the
cleared forms already contain a polynomial factor large enough to remove the
missing denominator charge.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel forms used in this content
calculation are due to Wadim Zudilin, *On the irrationality of generalized
q-logarithm*, Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, normalized forms,
backward-shift order lemma, and determinant estimate.  It does **not** state
the specialized `x=z=1` cyclotomic row content `G_n`, its all-rank
row-and-column divisibility, or the `N^3-N` charge ceiling.  Those polynomial
divisibility reductions, exact finite gcd regressions, degree comparison, and
the explicit one-way height conclusion are authored in this repository.

They do contain a universal factor, but it is decisively too small by itself.
Put

`P_n(p)=prod_(j=1)^n (p^j-1)` and
`L_n(p)=prod_(d=1)^n Phi_d(p)`.

Every coefficient of the source form `v_n(mu;p,1,1)` is divisible in `Z[p]`
by

`G_n(p)=p^(n+1) P_n(p)^3/L_n(p)`.

Consequently, with `H_n=P_n^3/L_n`,

`(prod_(i=0)^(N-1) H_i)^2 | V_N(mu;p,1,1)`.

This is a genuine all-rank denominator-factor opening.  Its degree, however,
is at most `N^3-N`, whereas the explicit `p=3/2` height comparison requires
more than `(39/41)(4N^3-3N^2)`.  Thus scalar row-and-column content alone is a
one-way no-go.  The surviving Hankel mechanism must find additional factors in
the primitive residual matrix, for example through the southeast-block route
isolated in `SoutheastBlockDeterminant.lean`.

## Why the row factor holds for every n

At `x=z=1`, the source clearing factor and the leading power in `A_n,B_n,C_n`
satisfy

`D_n(p) p^((n+1)(3n+2)/2) = p^(n+1) P_n(p)^3`.

The summand common to `A_n` and `B_n` is a monomial times

`[n+k choose k]_p [n choose k]_p`,

so it lies in `Z[p]`.  The only additional denominators in `B_n` are
`p^ell-1` with `1<=ell<=n`.  Each divides `L_n`, because
`p^ell-1=prod_(d|ell) Phi_d(p)`.  In `C_n`, both Gaussian binomials are already
polynomials, and its only denominators are `p^(n-ell)-1`, which are cleared by
the same `L_n`.  Therefore multiplying any of the three source sums by `L_n`
gives a polynomial, proving that `G_n` divides all three cleared coefficients.

The exact checker additionally finds that this guaranteed factor is the full
coefficient gcd for `0<=n<=4`; that finite exactness is regression evidence,
not needed by the all-rank divisibility argument.

## From row content to determinant content

For a cyclotomic polynomial `Phi_d`, its exponent in `H_n` is

`e_d(n)=max(3 floor(n/d)-1,0)`.

For nonnegative `i,j`, floor superadditivity gives
`floor((i+j)/d)>=floor(i/d)+floor(j/d)`.  A three-case check according as zero,
one, or both right-hand floors are positive yields

`e_d(i+j)>=e_d(i)+e_d(j)`.

Hence `H_i H_j | H_(i+j)`.  Pull `H_i` from row `i` and `H_j` from column `j`
of the Hankel matrix.  The determinant is divisible by the square of their
product.  This is precisely the row-and-column factorization mechanism already
kernel-checked abstractly by `det_diagonal_mul_mul_diagonal`.

## Exact charge ceiling

Since `deg P_n=n(n+1)/2` and `deg L_n=sum_(d<=n) phi(d)`, the guaranteed factor
has exact degree

`2 sum_(i=0)^(N-1) (3i(i+1)/2 - sum_(d<=i) phi(d))`.

Dropping the positive totient sum gives

`deg factor <= 3 sum_(i=0)^(N-1) i(i+1) = N^3-N`.

For every positive `N`,

`41(N^3-N) < 39(4N^3-3N^2)`.

The difference is
`N(115N^2-117N+41)>0`; the quadratic is positive because
`460(115N^2-117N+41)=(230N-117)^2+5171`.
`AdelicHeightBridge.lean` checks this strict comparison and its monotone
consumer: any extracted degree bounded by `N^3-N` misses the required charge.

## Executable evidence and boundary

Run:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_scalar_content.py \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_scalar_content_receipt.json
```

The checker reconstructs the displayed primary-source forms over `Z[p]`,
verifies their exact coefficient gcds through row index four, computes the
rank-one through rank-three Hankel contents, and records the exact factor-degree
table.  The source algebra above, rather than the finite scan, supplies the
all-rank factor.  Erdős #1049 remains open: this result eliminates only scalar
content as a sufficient mechanism and points to additional residual determinant
divisibility as the next distinct obligation.
