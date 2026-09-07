# Scalar moving-diagonal rational clearing at `3/2`

## Target and breadth gate

The programme target is irrationality of

`F(3/2) = sum_{k>=1} 1/((3/2)^k-1)`.

The exact open boundary was an all-index construction whose integral linear
forms decay after rational-base clearing.  Three structurally different
attacks were compared before this probe:

1. derive source-specific recombinations from the q-Apéry second-order
   recurrence; the finite analytic-aware selectors support this, while the
   determinant tradeoff shows that generic continued fractions merely restate
   irrationality;
2. change the scalar moving diagonal inside the shared little-`q`-Legendre
   kernel; Van Assche's positive norm identity supports this, while the
   homogeneous endpoint calculations suggest an unavoidable power-of-two tax;
3. impose the `2`-adic, `3`-adic, and real constraints simultaneously in a
   higher-rank congruence lattice; the moving-tail Plücker theorem supplies the
   local kernel, while the rapidly growing primitive remainders oppose a naive
   subset-sum argument.

The selected probe was attack 2 because the primary source already supplies
the analytic asymptotic and the local corpus already supplies exact endpoint
arithmetic.  Its falsifier was a fixed offset with a lower quadratic degree,
hidden even homogeneous numerator, or nonpositive cleared exponent.  Once all
fixed offsets share the same positive exponent, scalar Ore-operator
classification no longer has a route to the irrationality consumer and the
campaign must pivot to a growing offset or genuinely higher-rank construction.
The fixed-offset checkpoint landed as `a8c63830`; the next analytic pass below
then tests the entire outward range rather than scanning more offsets.

## Exact fixed-offset degree

Write `p=3/2`, `q=p^-1`, and evaluate Van Assche's little-`q`-Legendre
polynomial on

`x = p^(n+delta)`

for a fixed integer `delta >= 0`.  The `k`-th summand has degree

`2 n k - (k^2+k)/2 + delta k`.

Its forward difference is `2n-k-1+delta`, positive for `0<=k<n`.
Consequently the top summand is unique and

`D_(n,delta) = (3n^2+(2delta-1)n)/2`,

with leading coefficient `(-1)^n`.  Every fixed offset therefore has leading
quadratic degree `3n^2/2`; the offset changes only the linear term.

Let `d_m(p)=prod_{j<=m} Phi_j(p)` be the cyclotomic clearing polynomial needed
for the associated polynomial and the finite target tail.  For fixed `delta`,
`m=n+O(1)` and

`deg d_m = (3/pi^2)n^2+o(n^2)`.

The product `d_m(p) P_n(p^(n+delta)|p^-1)` has unit leading coefficient and
degree `D_(n,delta)+deg d_m`.  Homogeneous evaluation at `(3,2)` is therefore
odd.  Its reduced denominator is exactly

`2^(D_(n,delta)+deg d_m)`.

This is the exact denominator of the `P`-coefficient and therefore the forced
homogeneous multiplier.  It is not by itself a primitive-row theorem: after
both coefficients become integers, a common odd gcd may still divide the
entire row and its error.

## Source asymptotic composed with the clearing tax

Van Assche's positive squared-norm identity and bounds give the raw scalar
form quadratic exponent

`(3/pi^2-3/2) log(3/2)`.

The exact rational clearing adds

`(3/2+3/pi^2) log 2`.

Their sum is

`(3/2+3/pi^2) log 2 + (3/pi^2-3/2) log(3/2)`

`= (3/2) log(4/3) + (3/pi^2) log 3 > 0`.

`FixedDiagonalRationalClearing.lean` checks this identity and strict
positivity as
`fixedDiagonalRationalClearingExponent_eq_sourceBalance` and
`fixedDiagonalRationalClearingExponent_pos`.  It also checks the generic
consumer `not_tendsto_zero_of_eventually_one_le_abs`.

The exact checker independently materializes offsets `0,1,2,3` through
`n=7`, verifies every degree, unit leading coefficient, odd homogeneous
numerator, and exact reduced power-of-two denominator.  For Van Assche's
offset-zero diagonal, the primary source's exact positive error bounds put the
forced-cleared form above one for every displayed `n=2,...,7`.  The strengthened
checker also constructs the second coefficient and primitively normalizes the
exact pair; its finite rows stay above one as well, but this is finite evidence
rather than an all-index content bound.

## All outward scalar evaluations

Now let the evaluation exponent vary freely:

`x = p^m`, with `m >= n`.

In the `k`-th summand, the largest power of `p` is

`n k + m k - (k^2+k)/2`.

Its forward difference is `n+m-k-1`, which is positive for `0<=k<n`.
The endpoint `k=n` is therefore unique, with coefficient `(-1)^n`, and

`D_(n,m) = n m + n(n-1)/2`.

The target identity is still exact:

`f(p^m) = h_p(1) - sum_{j=1}^{m-1} 1/(p^j-1)`.

Consequently the finite target tail and the associated polynomial require the
cyclotomic cutoff

`M = max(n,m-1) = m+O(1)`.

Writing `E_M=deg d_M`, the coefficient `d_M(p)P_n(p^m|p^-1)` is a polynomial
of degree `D_(n,m)+E_M` with unit top coefficient.  At `p=3/2` it therefore has
exact reduced denominator `2^(D_(n,m)+E_M)`.  Thus `2^(D+E)` is the exact
homogeneous multiplier forced by that coefficient.  Once both coefficients
are integral, however, their common odd content can be divided out.  The
positive main term below becomes an all-outward no-go only after a
subquadratic, or quantitatively insufficient, primitive-content theorem.

Van Assche's Markov identity is valid for every `p^m>1`.  Its positive
squared-norm factor satisfies the exact bounds

`p^(n+1-m)/(p^(2n+1)-1) <= S_(n,m)`

and

`S_(n,m) <= p^(n+1)/((p^m-1)(p^(2n+1)-1))`.

The logarithm of this factor is only linear in `m+n`.  The two quadratic
inputs are instead

`log |P_n(p^m|p^-1)| = (n m+n^2/2+o(n^2)) log p`

and

`log d_M(p) = ((3/pi^2)m^2+o(m^2)) log p`.

After the forced power-of-two clearing, the main term is

`(n m+n^2/2) log(4/3) + (3/pi^2)m^2 log 3`.

Every factor is positive for `m>=n>=1`.  The omitted terms are
`o(n^2)+o(m^2)+O(m+n)`, so the **forced-homogeneous-cleared** error grows along
every sequence `m_n>=n`, including sequences for which `m_n/n` has no limit or
tends to infinity.  When `m_n/n -> beta`, division by `n^2` gives

`(beta+1/2) log(4/3) + (3/pi^2)beta^2 log 3 > 0`.

The Lean companion checks the finite-scale source-balance identity and strict
positivity as `movingDiagonalRationalClearingMainTerm_eq_sourceBalance` and
`movingDiagonalRationalClearingMainTerm_pos`.  It also checks the normalized
ratio formula, its positivity, and its specialization to the fixed-offset
exponent at `beta=1`.

The exact checker falsifies the intermediate algebra on the linearly moving
diagonals `m=n,2n,3n` through `n=6` and on `m=n^2` through `n=5`.  Every
displayed case has the predicted degree, unit endpoint, odd homogeneous
numerator, and exact forced denominator.  Van Assche's exact positive lower
bound exceeds one in every displayed outward case with `n>=2`.  Exact
primitive row content is `1` in twenty of the twenty-two displayed rows, `7`
at `(n,m)=(6,18)`, and `49` at `(4,16)`; every primitively normalized displayed
row with `n>=2` still has lower error bound greater than one.  This strongly
opposes a content repair but is not an asymptotic theorem.

## Adjacent determinant and the first all-index content reduction

The associated polynomial supplies more than the error identity.  If
`kappa_n` is the leading coefficient of `P_n` and `h_n` its squared norm,
the standard adjacent second-kind determinant is

`Q_n(z)P_(n-1)(z)-P_n(z)Q_(n-1)(z)
 = (kappa_n/kappa_(n-1)) h_(n-1)`.

The two factors are explicit in Van Assche's source:

`kappa_n=(-1)^n [2n choose n]_p p^(-n(n+1)/2)`

and

`h_(n-1)=p^n/(p^(2n-1)-1)`.

Taking the quotient of consecutive leading coefficients and cancelling gives
the exact all-index identity

`Q_n P_(n-1)-P_n Q_(n-1)=-(p^n+1)/(p^n-1)`.

Let `D_M` denote the odd homogeneous numerator of `d_M(3/2)`, and let
`G_(n,m)` be the common content of the two forced-cleared integer
coefficients.  If an odd prime `ell` does not divide `D_M`, all moment and
target-prefix denominators are `ell`-adic units.  Divisibility of both row
coefficients by `ell^t` therefore implies divisibility of both
`P_n(p^m)` and `Q_n(p^m)` by `ell^t`.  The adjacent determinant, whose
denominator `3^n-2^n` also divides `D_M`, then forces

`ell^t | 3^n+2^n`.

Consequently the largest divisor of `G_(n,m)` coprime to `D_M` divides
`3^n+2^n`.  This is exponentially linear in `n`, so it cannot repair the
quadratic forced-clearing deficit.  The entire unresolved quadratic content
is now confined to prime powers already supported on `D_M`.  The checker
reconstructs `P_n,Q_n` from the source moments and verifies the adjacent
identity exactly through `n=7`; it also verifies the divisor consequence on
every displayed primitive row.

A tempting further shortcut is false.  It is not true that every
clearing-supported content prime has multiplicative order at most `2n` for
the base `3/2`.  Exact witnesses include

- `(n,m,ell,ord_ell(3/2))=(4,32,11,10)`;
- `(5,40,31,30)`;
- `(7,28,43,21)`;
- `(8,64,59,58)`.

The precise next local statement comes from reducing the cleared coefficient
modulo `Phi_r`.  For `r>n`, put `L=floor((m-1)/r)`,
`C_r=d_M/Phi_r`, and `U_r=(p^r-1)/Phi_r`.  In
`Q[p]/(Phi_r)`, the associated-polynomial term vanishes and

`d_M (Q_n+P_n sum_(j<m) 1/(p^j-1))
 = P_n C_r U_r^(-1) H_L`,

where `H_L=sum_(a=1)^L 1/a`.  Indeed only indices `j=ar` survive and
`(p^(ar)-1)/(p^r-1)=1+p^r+...+p^((a-1)r)=a` modulo `Phi_r`.
At the rational specialization, cyclotomic resultants and possible vanishing
of `P_n(p^m)` prevent this congruence from immediately becoming a content
bound; the order counterexamples above come from exactly that boundary.  A
successful theorem must bound these harmonic, resultant, and `P_n` norm
contributions in aggregate, rather than merely restricting the order.

## Consequence and boundary

This eliminates denominator cancellation and the raw choice of outward
evaluation as repairs of the rational-base height problem: fixed, linear,
superlinear, and irregular outward offsets all have the same positive forced-
clearing mechanism.  It does **not** yet eliminate the scalar architecture,
because primitive common content is now the precise remaining escape hatch.
The adjacent determinant already removes every prime-power contribution away
from the clearing support up to the linear factor `3^n+2^n`.  The next theorem
must bound the remaining clearing-supported harmonic/resultant content below
the displayed positive main term; more outward scans without a proposed local
lemma are not useful.

The result also does not cover inward evaluations `m<n`.  Such an evaluation is not
automatically a construction for the original Lambert target: it must first
supply the exact finite-tail identity and denominator control, and its smaller
polynomial degree competes with a different cutoff.  Nonrectangular multiple
little-`q`-Jacobi systems, congruence-constrained combinations of several
rows, and determinant/Hankel constructions also remain genuinely distinct.

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_fixed_diagonal_rational_clearing.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_fixed_diagonal_rational_clearing.py --check
```

Canonical receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1049_fixed_diagonal_rational_clearing_receipt.json`.
