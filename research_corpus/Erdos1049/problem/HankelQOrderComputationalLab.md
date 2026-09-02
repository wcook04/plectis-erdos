# Zudilin Hankel q-order lab

## Analytic question

Zudilin's normalized forms at `x=z=1` are

`v_m^* = sum_(t>=0) q^((m+1)t) (q;q)_m^3 (q^(t+1);q)_m /
(q^(m+1+t);q)_(m+1)`.

The primary-source row transformation proves

`ord_q V_N^* >= N(N-1)(2N-1)/6`

for the Hankel determinant `V_N^*=det(v_(i+j)^*)`.  Any additional cubic
order would strengthen the analytic decay before denominator clearing and
would therefore attack the explicit `p=3/2` height deficit from the analytic
side.  Equality sends the method back to arithmetic factor extraction.

## Source and attribution boundary

The source-normalized forms, Hankel determinant, backward-shift operator, and
lower-bound row transformation used here are due to Wadim Zudilin, *On the
irrationality of generalized q-logarithm*, Research in Number Theory 2 (2016),
Article 15, DOI [10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).
The downloaded primary source is retained at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section
4, source TeX lines 278--380, defines `V_n`, `v_n^*`, `D_l`, proves the
backward-shift order lemma, and derives the determinant lower bound.  It does
**not** state the associated-graded transformed-row coefficient, the
Vandermonde leading matrix, or the tail-index reciprocal-state identity
recorded here.  Those exact leading coefficients, finite rank-7 replay, and
the explicit boundary between the source lower bound and the stronger
assertion are authored in this repository.

## Exact probe

`scripts/check_zudilin_hankel_qorder.py` expands the displayed source formula
as a truncated integer formal power series.  Multiplication by `1-q^k` and
division by `1-q^k` are performed coefficientwise; the latter uses the exact
recurrence `b_d=a_d+b_(d-k)`.  The checker then evaluates the determinant by
the Leibniz formula, retaining eight coefficients beyond the source bound.

Canonical receipt:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_zudilin_hankel_qorder.py \
  --max-rank 7 --margin 8 \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_hankel_qorder_receipt.json
```

The receipt hashes the checker, the local primary-source extraction, and the
Lean threshold consumer.  Its bounded resource contract records rank `7`,
Hankel moment indices through `12`, cutoff degree `99`, and at most `7!`
permutations.

## Result and structure

For every exact rank `1 <= N <= 7`, the first nonzero determinant coefficient
occurs exactly at the source lower bound:

| `N` | source/computed order | leading coefficient |
|---:|---:|---:|
| 1 | 0 | 1 |
| 2 | 1 | 6 |
| 3 | 5 | 108 |
| 4 | 14 | 4320 |
| 5 | 30 | 324000 |
| 6 | 55 | 40824000 |
| 7 | 91 | 8001504000 |

These coefficients are structured.  Their successive ratios are
`N^2(N+1)/2`, and all seven equal

`(N!)^2 (N+1)! / 2^N`.

The stronger transformed-row probe explains both patterns.  Applying the
source operator `D_j=(N;q)_j` directly to every entry through the full rank-7
grid gives

`D_j v_(j+l)^* = (-1)^j (j+1)^2(j+2)/2 *
q^(j(j+1)/2+jl) + O(q^(j(j+1)/2+jl+1))`.

After the row factors are removed, the leading matrix is `((q^j)^l)`, a
Vandermonde matrix.  Its order is `N(N-1)(N-2)/6`; the row factors contribute
`N(N-1)(N+1)/6`, giving the source order exactly.  The row coefficient product
is the displayed factorial coefficient.  The two fan-in identities are exact
finite-product and polynomial algebra; the proof-bearing gap is not those
identities but the arbitrary-`j,l` transformed-row leading term.

The tail-index decomposition closes that remaining assertion.  For a formal
series `H(X)=1+sum_(r>=1) a_r X^r`, set

`w_n(H,t)=q^((n+1)t) prod_(k=1)^n H(q^k)`.

Track the associated-graded coefficient in the source proof of Lemma 1, not
just its lower bound.  After one more operator factor, a positive tail state
`t` moves to `t-1` with coefficient `-1`, while state zero emits state `s-1`
with coefficient `a_s`.  If `c_(j,t)` is the coefficient of state zero after
`j` steps and `h_r=[X^r]H(X)^(-1)`, this gives

`c_(0,t)=1_(t=0)`,

`c_(j+1,t)=-c_(j,t-1)` for `t>0`,

`c_(j+1,0)=sum_(s>=1) a_s c_(j,s-1)`.

The reciprocal relation
`h_(r+1)=-sum_(s=1)^(r+1) a_s h_(r+1-s)` now proves by induction

`c_(j,t)=(-1)^j h_(j-t)` for `t<=j`, and zero otherwise.

`AdelicHeightBridge.lean::hankelAssociatedCoeff_eq_reciprocal` kernel-checks
this all-depth recurrence solution.  It is the associated-graded sharpening
of the primary source's Lemma 1; it is not a finite-rank extrapolation.
The actual positive- and zero-tail ratios and their reciprocal series are now
Lean objects too.  Lean proves both inverse-product identities, derives the
triangular and adjacent-tetrahedral reciprocal coefficients, specializes the
all-depth recurrence to each source state, and proves their exact fan-in as
`AdelicHeightBridge.lean::zudilinAssociatedTailRowCoeff_eq`.

For the actual normalized summand with tail index `t`, the ratio of consecutive
indices is

`q^t H_t(q^n)`, where

`H_t(X)=(1-X)^3(1-q^t X)^2 / ((1-q^t X^2)(1-q^(t+1)X^2))`.

Only its specialization at `q=0` enters the associated grade.  For `t>=1`,
`H_t(X)=(1-X)^3`, so the contribution is
`(-1)^j binom(j-t+2,2)`.  For `t=0`,
`H_0(X)=(1-X)^4/(1+X)`, so the contribution is

`(-1)^j (j+1)(j+2)(2j+3)/6`.

Summing `0<=t<=j` yields exactly

`(-1)^j (j+1)^2(j+2)/2`.

The literal source tails are connected to those associated states by an exact
consecutive-index identity, not merely by a formal specialization.  If
`T_(n,t)` denotes the normalized `t`th tail, Lean proves

`T_(n+1,t)=X^t T_(n,t) U_(n,t)`, where

`U_(n,t)=(1-X^(n+1))^3(1-X^(n+t+1))^2 /
((1-X^(2n+t+2))(1-X^(2n+t+3)))`.

The two denominator factors clear exactly, and
`AdelicHeightBridge.lean::coeff_zudilinNormalizedTailStepUnit_first` proves
`[X^(n+1)]U_(n,t)=-5` for `t=0` and `-3` for every `t>0`.  Thus neither the
hypergeometric step ratio nor its first associated-grade coefficient remains
an unformalized premise.

Lean now also proves `U_(n,t)-1` has no coefficient below degree `n+1`.
The exact Gaussian-binomial coefficients satisfy
`D_(j+1)=(1-X^jN)D_j` on every power-series sequence, and hence the literal
transformed moments satisfy

`D_(j+1)v_(j+1+l)^*=D_jv_(j+l+1)^*-X^jD_jv_(j+l)^*`.

This bridge already closes the first nontrivial row in every column:
`AdelicHeightBridge.lean::order_zudilinTransformedNormalizedMoment_one`
proves `ord(D_1v_(l+1)^*)=l+1`, while
`coeff_zudilinTransformedNormalizedMoment_one_first` gives leading coefficient
`-6`, exactly `(-1)^1(2^2·3/2)`.  The remaining iteration starts at row
`j=2`; row `j=1` is no longer part of the formal boundary.

The checker now records every individual tail contribution throughout the
full transformed rank-seven grid, rather than only their sum.
`zudilinTransformedTailNumerators_add` kernel-checks the final polynomial
fan-in.

Lean also checks the algebra after the associated-grade row statement has
been obtained.  In
`AdelicHeightBridge.lean::zudilinSharpHankelOrderAndCoeff_algebraicAssembly`,
the exact all-rank exponent identity and the scaled row-coefficient product
are assembled as

`6 * ord_q(V_N^*) = N(N-1)(2N-1)`

and

`2^N * lc_q(V_N^*) = (N!)^2 (N+1)!`.

The determinant passage is now kernel checked too.  Lean defines the exact
Gaussian-binomial coefficients of the source `D_j` operator, packages the
row operations as a lower-unitriangular matrix of determinant one, and proves
that it preserves every power-series Hankel determinant in
`det_zudilinBackwardShiftedMomentMatrix`.  The exact normalized source summand
is now also a Lean object: its shift is `(n+1)t`, every lower coefficient
vanishes, and its coefficient at that shift is exactly one.  The normalized
moment is defined coefficientwise by the exact finite tail range, has constant
coefficient one, and below degree `n+1` receives only the zero-tail
contribution.  Lean then defines the signed associated-graded matrix,
identifies it with a diagonal row scaling of the power-series Vandermonde
matrix, proves its exact determinant product and all-rank noncancellation,
computes its exact power-series order, reduces that order to `sum_(j<N) j^2`,
and closes the displayed division-free formula in
`six_mul_order_det_zudilinAssociatedLeadingMatrix`.  A generic filtered
determinant theorem additionally proves that entrywise exact orders and one
uniquely minimizing Leibniz permutation force the determinant's exact order.
The focused `AdelicHeightBridge` build and final serialized replay pass.  The
sole remaining formal boundary is the initial-monomial theorem for every row
`j>=2` and column `l`, iterating the now-exact tail-step and source-operator
identities through the filtered shifts and identifying the resulting entries
with this kernel-checked associated-grade matrix.  The reciprocal
specialization, row-scalar fan-in, exact consecutive tail recurrence, first
source-step coefficient, and complete all-column row `j=1` are kernel checked.

The transformed determinant is therefore a row-factor product times the
Vandermonde determinant `det(q^(jl))`.  Its lowest monomial is nonzero: each
factor `q^b-q^a` (`a<b`) begins with `-q^a`.  The Vandermonde sign cancels the
product of the row signs, its order is `N(N-1)(N-2)/6`, and the total leading
coefficient is

`(N!)^2 (N+1)! / 2^N`.

Hence Zudilin's normalized Hankel lower bound is sharp at `x=z=1` for every
rank.  Hidden normalized-Hankel `q`-order is decisively eliminated as a source
of the missing cubic gain; the surviving route must extract arithmetic
denominator factors or change the integral model.

## Claim boundary and next analytic consequence

The all-rank mathematical result does **not** compute a denominator factor or
prove irrationality at `p=3/2`.  Its recurrence fan-in, exact source
backward-shift coefficients, determinant preservation, associated-grade
determinant product, noncancellation, exact order, closed exponent, and
factorial-product assembly are Lean checked.  The entrywise theorem giving
the claimed initial monomial of each shifted normalized moment is not; the
exact source tails, their first monomials, coefficientwise normalized moments,
source determinant preservation, and the generic unique-minimum determinant
consumer are.  The theorem closes one mechanism: free analytic improvement
from a larger normalized `q`-order cannot occur.  All useful improvement in
this Hankel family must now come from arithmetic removal of the raw denominator
charge, or from a genuinely different integral construction.
