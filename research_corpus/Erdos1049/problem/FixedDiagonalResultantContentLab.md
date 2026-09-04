# Fixed-diagonal resultant control of primitive content

The scalar Van Assche construction at `p=3/2` has one precise arithmetic
escape: after the forced power-of-two clearing, the two integer coefficients
may have a large common odd content.  A local attempt to bound each valuation
by the cyclotomic clearing valuation is false.  At `(n,m,ell)=(4,16,7)`, the
row content has `v_7=2` while the clearing numerator has `v_7=1`; the extra
valuation comes from the `P_n`/harmonic block.

For the original diagonal `m=n`, there is a global replacement.  Put

`A_n(p)=d_n(p)P_n(p^n|p^-1)`

and

`C_n(p)=d_n(p)(Q_n(p^n)+P_n(p^n) sum_(j<n)1/(p^j-1))`.

Both are in `Z[p]`.  If `W_n=deg A_n`, then `deg C_n=W_n-1`, and their
homogeneous evaluations with common width `W_n` at `(3,2)` are exactly the two
forced-cleared integer coefficients.  If an odd integer `g` divides both
evaluations, then `p=3/2` is a common root of `A_n` and `C_n` modulo every
prime power of `g`.  Therefore

`g | Res_p(A_n,C_n)`.

This single resultant sees clearing-supported primes, harmonic gains, and
primes away from the clearing support at once.  It avoids the false local
valuation shortcut.

There is also an exact multiplicative decomposition.  If
`Qtilde_n=d_n Q_n(p^n)`, then reduction modulo the two factors of
`A_n=d_nP_n` gives

`Res(A_n,C_n)=Res(d_n,C_n) Res(P_n(p^n),Qtilde_n)`.

The second factor is `1` through `n=5`, but it is `5` at `n=6` and `16` at
`n=7`.  Thus the tempting unit-resultant shortcut is false.  The split is
still useful: an all-index proof may bound the cyclotomic-harmonic and
associated-Pade factors separately.

## Exact top cyclotomic factor

One local factor has a closed form at every rank:

`|Res_p(Phi_n,C_n)|=2^phi(n)`.

Here is a direct proof.  In `C_n=d_n(Q_n+P_n S_(n-1))`, every denominator in
the finite prefix has index `<n`; after multiplication by `d_n`, its term is
still divisible by `Phi_n` and vanishes modulo `Phi_n`.  The same holds for
every moment in `Q_n` except the top moment `j=n`.  That moment occurs only in
the top coefficient of `P_n`, so modulo `Phi_n` the surviving factor is

`(-1)^n p^(-n(n+1)/2) [2n choose n]_p p^n d_n/(p^n-1)`.

At a primitive `n`-th root, the factors in the Gaussian quotient cancel for
`j<n`, while its last factor is

`(1-p^(2n))/(1-p^n)=1+p^n=2`.

Thus `[2n choose n]_p=2 mod Phi_n`.  The monomial has absolute norm one.
Finally,

`d_n/(p^n-1)=prod_(s<=n, s not_dvd n) Phi_s`.

Every factor in this product has resultant of absolute value one against
`Phi_n`: a nontrivial cyclotomic resultant could occur only if `n/s` were a
prime power, which would force `s|n`, contrary to the product condition.
Taking norms gives the formula.  The checker independently verifies it at
every displayed rank.

This factor contributes only `phi(n)log 2=O(n)` to the rank-`n` resultant, so
it is not part of the unresolved quadratic mass.  The proof also supplies the
template for the remaining `Phi_r` factors: isolate the moments with indices
divisible by `r`, then combine their root-of-unity norm with the explicit
cross-cyclotomic resultant.

The adjacent local factor has an equally exact formula.  For every `n>=3`,

`|Res_p(Phi_(n-1),C_n)|=3^phi(n-1)`.

Write `r=n-1` and work modulo `Phi_r`.  Now `p^n=p`.  The first q-binomial in
the coefficient of `x^k` vanishes for `2<=k<=r-1`, so only
`k=0,1,r,n` survive.  Direct cancellation in the two endpoint Gaussian
coefficients gives

`c_r=-2`, `c_n p=2(1+p)`.

The only surviving denominator is the moment/prefix index `j=r`.  Its
`Q_n` contribution is `c_r+c_n p`, while the prefix contribution is

`P_n(p)=-p+c_r+c_n p`.

Their sum is therefore

`-p+2c_r+2c_n p=3p`.

As in the top-index proof, the remaining factor `d_n/(p^r-1)` has norm one
against `Phi_r`: a nontrivial cyclotomic resultant would force an excluded
divisibility relation among its indices.  Since the monomial `p` also has
absolute norm one, the claimed `3^phi(r)` follows.  The exceptional small
case `r=2` is included by direct evaluation and is replayed by the checker.

Together the top two factors contribute only `O(n)` to the logarithm.  Any
quadratic resultant mass must therefore come from indices `r<=n-2` or from
the separate associated-Pade factor.

## The all-index local product law

The root-of-unity factor missing from the first global bound can in fact be
identified exactly.  Write

`n=a r+b`, with `0<=b<r`, and put `H_a=sum_(t=1)^a 1/t`.  Then in
`Q[p]/(Phi_r)` one has

`C_n = (-1)^a (d_n/(p^r-1)) P_b(p^b) K_(a,b)`,

where `K_(a,b)=3H_a` if `b>0`, and
`K_(a,0)=3H_a-1/a`.  Consequently

`|Res(Phi_r,C_n)|`

`= |Res(Phi_r,d_n/(p^r-1))| K_(a,b)^phi(r)`

`  * |Res(Phi_r,P_b(p^b))|`.

The factors on the right are rational individually when `K_(a,b)` is not an
integer, but their product is the integral resultant on the left.  This is an
identity for every `1<=r<=n`, not a finite extrapolation.

To prove it, write the diagonal polynomial as `P_n(p^n)=sum_k u_k`, where

`u_k=(-1)^k [n choose k]_p [n+k choose k]_p p^(k(k-1)/2)`.

At a primitive `r`-th root, q-Lucas with `k=cr+d` gives

`u_(cr+d)=(-1)^c binom(a,c)binom(a+c,c) u_d^(b)`.

Here `u_d^(b)` is the corresponding diagonal summand for `P_b(p^b)`.
Terms with `b+d>=r` vanish on both sides, so this formula needs no additional
range case.  If

`lambda_c=(-1)^c binom(a,c)binom(a+c,c)`,

then `sum_c lambda_c=(-1)^a`.  In `C_n`, multiplication by `d_n` kills every
moment except those with index `tr`.  Moreover

`d_n/(p^(tr)-1) = (1/t) d_n/(p^r-1) mod Phi_r`.

The surviving moment tails therefore contribute

`sum_(t=1)^a (1/t) sum_(c=t)^a lambda_c`

times `P_b(p^b)`, while the finite Lambert prefix contributes
`(-1)^a H_a` when `b>0` and `(-1)^a H_(a-1)` when `b=0`.  Finally the
binomial-harmonic identity

`sum_(c=1)^a lambda_c H_c=(-1)^a 2H_a`

gives exactly the two displayed scalars.  For completeness, this last identity
is the derivative at `gamma=1` of Chu--Vandermonde

`sum_c (-a)_c(a+1)_c/(c!(gamma)_c)`

`= (gamma-a-1)_a/(gamma)_a`.

Differentiating the summand contributes `-H_c`; the logarithmic derivative of
the right side is `-2H_a`, and its value at `gamma=1` is `(-1)^a`.
The checker reconstructs `C_n` and replays the complete factorization
independently for every `1<=r<=n<=7`.

This law contains the earlier top formulas: `(a,b)=(1,0)` gives the scalar
`2`, and `(a,b)=(1,1)` gives `3` together with the unit-norm polynomial
`P_1(p)=-p`.

It also corrects the asymptotic bookkeeping.  The exact product of the
cross-cyclotomic norms `|Res(Phi_r,d_n/(p^r-1))|` has quadratic constant

`(3/pi^2) sum_prime log(p)/(p^2-1)=0.17324...`,

half the constant of the deliberately symmetric overbound `X_n` below.  The
harmonic scalars have quadratic constant

`(3/pi^2) sum_(a>=1) log(3H_a)(1/a^2-1/(a+1)^2)`

`=0.376904214...`.

Their combined constant is about `0.55015`, leaving a genuine quadratic
margin below the forced-clearing exponent.  The unresolved cyclotomic
contribution is now the explicit smaller-diagonal product

`prod_(r<=n)|Res(Phi_r,P_(n mod r)(p^(n mod r)))|`.

Thus the route no longer lacks a local formula.  It lacks a subcritical
aggregate bound for this residual product, together with the separate
associated-Pade factor.

The exact product law decides that question negatively for the *full*
resultant.  Evaluating its three displayed factors for `1<=n<=15`, without
constructing the large polynomial `C_n`, gives the first budget crossing at
`n=15`:

`log|Res(d_15,C_15)|/15^2 = 0.776255453400277`

`> 0.765461201033283`.

The exact decomposition at that rank is

- cross-cyclotomic product `6507824566763520000`;
- harmonic product
  `7447503819603964423447369356985205387964370413 / 266240000`;
- smaller-diagonal norm product `39138594322160874167`.

Their product is the integer

`7124895365541918046801279337807456559195210914326234110922619357146702910208`.

This crossing occurs before multiplication by the separate associated-Pade
factor.  Hence a globally subcritical upper bound for the full resultant is
false, not merely unproved.  Resultant divisibility can still organize which
primes are available to the specialized content, but its absolute magnitude
cannot close the scalar argument.  A continuation would have to prove that
the particular homogeneous value at `(3,2)` selects only a subcritical part
of the resultant, or abandon this scalar fixed diagonal.

## A precise global bound, and its exact falsifier

The cyclotomic resultant law makes the cross-factor

`X_n=prod_(r!=s<=n)|Res(Phi_r,Phi_s)|`

explicit.  Its logarithmic quadratic constant is

`(6/pi^2) sum_p log(p)/(p^2-1)=0.34649...`.

The first plausible global completion was

`|Res(d_n,C_n)| <= X_n prod_(r<=n)(floor(n/r)+1)^phi(r)`.

The second product has quadratic constant `0.30396...`, so this inequality
would have bounded the clearing-numerator resultant at about `0.65045 n^2`,
comfortably below the forced-clearing exponent.  It survives through `n=9`,
but only barely there: the exact multiplicative slack is
`1.0602164776752796`.

At `n=10` it is false.  Exact symbolic construction gives

`Res(d_10,C_10)=2^16 3^26 5 7^2 11^2 13^2 17 19 7297`

in absolute value.  The logarithmic rates divided by `10^2` are

- full clearing resultant: `0.6975409277238279`;
- cross-cyclotomic factor: `0.3933752152908670`;
- proposed quotient bound: `0.28803155168593664`.

Thus the right-hand side is only `0.19920594802733943` times the left-hand
side.  At this rank the actual full rate remains below `0.7654612010...`; the
all-index local product law above supplies the omitted factor exactly.  Its
later `n=15` crossing is the decisive falsifier for the full-resultant height
route.

The exact table is:

| `n` | `(deg A_n,deg C_n)` | factorization of `|Res(A_n,C_n)|` | `log|Res|/n^2` |
|---:|---:|---:|---:|
| 1 | `(2,1)` | `2` | `0.693147` |
| 2 | `(7,6)` | `2^4` | `0.693147` |
| 3 | `(16,15)` | `2^2 3 31` | `0.657655` |
| 4 | `(28,27)` | `2^8 3^4` | `0.621227` |
| 5 | `(45,44)` | `2^4 3^7 7 19` | `0.614129` |
| 6 | `(63,62)` | `2^8 3^6 5^2 31 431` | `0.690440` |
| 7 | `(88,87)` | `2^14 3^14 11 1069` | `0.703205` |

Every pair is coprime in `Z[p]`, every exact row content divides the displayed
resultant, and every displayed rate is below

`(3/2)log(4/3)+(3/pi^2)log 3 = 0.7655...`,

the positive fixed-diagonal forced-clearing exponent.  The comparison is
finite evidence only, and the exact `n=15` local-product evaluation shows that
it cannot extend to the desired all-index full-resultant bound.  The remaining
scalar target, if pursued, must be a specialization-selective theorem bounding
the actual row content strictly below the resultant.  Otherwise #1049 requires
the genuinely coupled selector construction.

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_fixed_diagonal_resultant_content.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_fixed_diagonal_resultant_content.py --check
```

Canonical receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1049_fixed_diagonal_resultant_content_receipt.json`.
